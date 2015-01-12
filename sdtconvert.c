/*-
 * Copyright (c) 2015 Mark Johnston <markj@FreeBSD.org>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice unmodified, this list of conditions, and the following
 *    disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <sys/cdefs.h>
__FBSDID("$FreeBSD$");

#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/queue.h>
#include <sys/sdt.h>

#include <assert.h>
#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <gelf.h>
#include <libelf.h>

#define	ELF_ERR()	(elf_errmsg(elf_errno()))
#define	LOG(...) do {					\
	if (verbose)					\
		warnx(__VA_ARGS__);			\
} while (0)

#define	AMD64_CALL	0xe8
#define	AMD64_JMP32	0xe9
#define	AMD64_NOP	0x90
#define	AMD64_RETQ	0xc3

static const char probe_prefix[] = "__dtrace_probe_";
static const char sdtobj_prefix[] = "sdt_";
static const char sdtinst_prefix[] = "sdt$";

static bool verbose = false;

struct probe_instance {
	const char	*symname;
	uint64_t	offset;
	SLIST_ENTRY(probe_instance) next;
};

SLIST_HEAD(probe_list, probe_instance);

static Elf_Scn *add_section(Elf *, const char *, uint64_t, uint64_t);
static Elf_Scn *add_reloc_section(Elf *, Elf_Scn *, Elf_Scn *);
static size_t	append_data(Elf *, Elf_Scn *, const void *, size_t);
static size_t	expand_section(Elf_Scn *, size_t);
static Elf_Scn *get_reloc_section(Elf *e, Elf_Scn *);
static const char *get_section_name(Elf *, Elf_Scn *);
static void	init_new_sections(Elf *, Elf_Scn *, Elf_Scn **, Elf_Scn **,
		    size_t);
static int	process_reloc(Elf *, GElf_Ehdr *, GElf_Shdr *, Elf_Scn *,
		    uint8_t *, GElf_Addr, GElf_Xword *, struct probe_list *);
static void	process_reloc_section(Elf *, GElf_Ehdr *, GElf_Shdr *,
		    Elf_Scn *, struct probe_list *);
static void	process_obj(const char *);
static void	record_instance(Elf *, GElf_Ehdr *, Elf_Scn *, Elf_Scn *,
		    Elf_Scn *, Elf_Scn *, const struct probe_instance *, int,
		    const char *);
static Elf_Scn *section_by_name(Elf *, const char *);
static int	symbol_by_name(Elf *, Elf_Scn *, const char *, GElf_Sym *,
		    uint64_t *);
static GElf_Sym	*symbol_by_index(Elf_Scn *, int);
static void	usage(void);
static int	wordsize(Elf *);
static void *	xmalloc(size_t);

static Elf_Scn *
add_section(Elf *e, const char *name, uint64_t type, uint64_t flags)
{
	GElf_Shdr newshdr, strshdr;
	Elf_Data *strdata;
	Elf_Scn *newscn, *strscn;
	size_t off, shdrstrndx;

	/* First add the section name to the section header string table. */
	if (elf_getshdrstrndx(e, &shdrstrndx) != 0)
		errx(1, "elf_getshdrstrndx: %s", ELF_ERR());
	if ((strscn = elf_getscn(e, shdrstrndx)) == NULL)
		errx(1, "elf_getscn on shdrstrtab: %s", ELF_ERR());
	if (gelf_getshdr(strscn, &strshdr) != &strshdr)
		errx(1, "gelf_getshdr on shdrstrtab: %s", ELF_ERR());
	if ((strdata = elf_getdata(strscn, NULL)) == NULL)
		errx(1, "elf_getdata on shdrstrtab: %s", ELF_ERR());

	off = append_data(e, strscn, name, strlen(name) + 1);

	/* Then create the actual section. */
	if ((newscn = elf_newscn(e)) == NULL)
		errx(1, "elf_newscn: %s", ELF_ERR());
	if (gelf_getshdr(newscn, &newshdr) != &newshdr)
		errx(1, "gelf_getshdr: %s", ELF_ERR());

	newshdr.sh_name = off;
	newshdr.sh_type = type;
	newshdr.sh_flags = flags;
	newshdr.sh_addralign = 8;

	if (gelf_update_shdr(newscn, &newshdr) == 0)
		errx(1, "gelf_update_shdr: %s", ELF_ERR());

	LOG("added section %s", name);

	return (newscn);
}

static Elf_Scn *
add_reloc_section(Elf *e, Elf_Scn *scn, Elf_Scn *symscn)
{
	GElf_Shdr relshdr;
	Elf_Scn *relscn;
	const char *scnname;
	char *relscnname;
	size_t sz, shndx, symndx;

	scnname = get_section_name(e, scn);

	sz = strlen(".rela") + strlen(scnname) + 1;
	relscnname = xmalloc(sz);
	(void)strlcpy(relscnname, ".rela", sz);
	(void)strlcat(relscnname, scnname, sz);

	relscn = add_section(e, relscnname, SHT_RELA, 0);
	if (gelf_getshdr(relscn, &relshdr) != &relshdr)
		errx(1, "couldn't get section header for %s: %s", relscnname,
		    ELF_ERR());

	if ((shndx = elf_ndxscn(scn)) == SHN_UNDEF)
		errx(1, "couldn't get section index for %s: %s", scnname,
		    ELF_ERR());
	if ((symndx = elf_ndxscn(symscn)) == SHN_UNDEF)
		errx(1, "couldn't get section index for %s: %s",
		    get_section_name(e, symscn), ELF_ERR());

	relshdr.sh_info = shndx;
	relshdr.sh_link = symndx;
	if (gelf_update_shdr(relscn, &relshdr) == 0)
		errx(1, "updating section header for %s: %s", relscnname,
		    ELF_ERR());
	return (relscn);
}

/*
 * Append arbitrary data to an ELF section, returning the original size of the
 * section.
 */
static size_t
append_data(Elf *e, Elf_Scn *scn, const void *data, size_t sz)
{
	GElf_Shdr shdr;
	Elf_Data *newdata;

	if (gelf_getshdr(scn, &shdr) != &shdr)
		errx(1, "failed to get section header for %s: %s",
		    get_section_name(e, scn), ELF_ERR());
	if ((newdata = elf_newdata(scn)) == NULL)
		errx(1, "failed to allocate new data descriptor for %s: %s",
		    get_section_name(e, scn), ELF_ERR());

	/* No need to set d_off since we let libelf handle the layout. */
	newdata->d_align = shdr.sh_addralign;
	newdata->d_buf = xmalloc(sz);
	newdata->d_size = sz;
	memcpy(newdata->d_buf, data, sz);
	return (expand_section(scn, sz));
}

/* Add sz bytes to the section size, returning the original size. */
static size_t
expand_section(Elf_Scn *scn, size_t sz)
{
	GElf_Shdr shdr;

	if (gelf_getshdr(scn, &shdr) != &shdr)
		errx(1, "gelf_getshdr: %s", ELF_ERR());
	shdr.sh_size += sz;
	if (gelf_update_shdr(scn, &shdr) == 0)
		errx(1, "gelf_update_shdr: %s", ELF_ERR());
	return (shdr.sh_size - sz);
}

/*
 * Find the relocation section associated with a given ELF section.
 * XXX there can probably be multiple relocation sections...
 */
static Elf_Scn *
get_reloc_section(Elf *e, Elf_Scn *scn)
{
	GElf_Shdr shdr;
	Elf_Scn *relscn;
	size_t shndx;

	if ((shndx = elf_ndxscn(scn)) == SHN_UNDEF)
		errx(1, "couldn't get section index for %s: %s",
		    get_section_name(e, scn), ELF_ERR());

	for (relscn = NULL; (relscn = elf_nextscn(e, relscn)) != NULL; ) {
		if (gelf_getshdr(relscn, &shdr) == NULL)
			errx(1, "gelf_getshdr: %s", ELF_ERR());

		if ((shdr.sh_type == SHT_REL || shdr.sh_type == SHT_RELA) &&
		    shdr.sh_info == shndx)
			return (relscn);
	}
	return (NULL);
}

/* Return the name of the specified section. */
static const char *
get_section_name(Elf *e, Elf_Scn *scn)
{
	GElf_Shdr shdr;
	size_t ndx;

	if (gelf_getshdr(scn, &shdr) != &shdr)
		errx(1, "gelf_getshdr: %s", ELF_ERR());
	if (elf_getshdrstrndx(e, &ndx) != 0)
		errx(1, "elf_getshdrstrndx: %s", ELF_ERR());
	return (elf_strptr(e, ndx, shdr.sh_name));
}

/*
 * Create a linker set for the set of probe instances (set_sdt_instances_set),
 * and create a relocation section for it.
 */
static void
init_new_sections(Elf *e, Elf_Scn *symscn, Elf_Scn **instscn,
    Elf_Scn **instrelscn, size_t scnsz)
{
	Elf64_Sym sym64;
	Elf32_Sym sym32;
	GElf_Shdr symshdr;
	Elf_Data *data;
	Elf_Scn *strscn;
	const char *startset, *stopset;
	void *sym;
	size_t startoff, stopoff, symsz;

	*instscn = add_section(e, "set_sdt_instances_set", SHT_PROGBITS,
	    SHF_ALLOC);

	if ((data = elf_newdata(*instscn)) == NULL)
		errx(1, "failed to add data section: %s", ELF_ERR());

	data->d_align = wordsize(e);
	data->d_buf = xmalloc(scnsz);
	data->d_size = scnsz;
	memset(data->d_buf, 0, scnsz);

	assert(expand_section(*instscn, data->d_size) == 0);

	*instrelscn = add_reloc_section(e, *instscn, symscn);

	/*
	 * It turns out that the kernel expects a pair of symbols to denote the
	 * boundaries of the linker set. Some deep magicks are at work here
	 * though: all we need to do is define the symbols, and the linker takes
	 * care of the rest. Not yet sure how that actually works.
	 */
	if (gelf_getshdr(symscn, &symshdr) != &symshdr)
		errx(1, "failed to look up section header for %s: %s",
		    get_section_name(e, symscn), ELF_ERR());
	if ((strscn = elf_getscn(e, symshdr.sh_link)) == NULL)
		errx(1, "failed to find string table for %s: %s",
		    get_section_name(e, symscn), ELF_ERR());

	startset = "__start_set_sdt_instances_set";
	startoff = append_data(e, strscn, startset, strlen(startset) + 1);
	stopset = "__stop_set_sdt_instances_set";
	stopoff = append_data(e, strscn, stopset, strlen(stopset) + 1);

	switch (gelf_getclass(e)) {
	case ELFCLASS32:
		memset(&sym32, 0, sizeof(sym32));
		sym32.st_info = ELF32_ST_INFO(STB_WEAK, STT_NOTYPE);

		symsz = sizeof(sym32);
		sym = &sym32;
		break;
	case ELFCLASS64:
		memset(&sym64, 0, sizeof(sym64));
		sym64.st_info = ELF64_ST_INFO(STB_WEAK, STT_NOTYPE);

		symsz = sizeof(sym64);
		sym = &sym64;
		break;
	default:
		errx(1, "unexpected ELF class %d", gelf_getclass(e));
	}

	sym32.st_name = startoff;
	sym64.st_name = startoff;
	append_data(e, symscn, sym, symsz);

	sym32.st_name = stopoff;
	sym64.st_name = stopoff;
	append_data(e, symscn, sym, symsz);
}

static int
process_reloc(Elf *e, GElf_Ehdr *ehdr, GElf_Shdr *symshdr, Elf_Scn *symtab,
    uint8_t *target, GElf_Addr offset, GElf_Xword *info,
    struct probe_list *plist)
{
	struct probe_instance *inst;
	GElf_Sym *sym;
	char *symname;
	uint8_t opc;

	sym = symbol_by_index(symtab, GELF_R_SYM(*info));
	symname = elf_strptr(e, symshdr->sh_link, sym->st_name);
	if (symname == NULL)
		errx(1, "elf_strptr: %s", ELF_ERR());

	if (strncmp(symname, probe_prefix, sizeof(probe_prefix) - 1) != 0)
		/* We're not interested in this relocation. */
		return (1);

	/* Sanity checks. */
	if (GELF_ST_TYPE(sym->st_info) != STT_NOTYPE)
		errx(1, "unexpected symbol type %d for %s",
		    GELF_ST_TYPE(sym->st_info), symname);
	if (GELF_ST_BIND(sym->st_info) != STB_GLOBAL)
		errx(1, "unexpected binding %d for %s",
		    GELF_ST_BIND(sym->st_info), symname);

	switch (ehdr->e_machine) {
	case EM_X86_64:
		/* Sanity checks. */
		opc = target[offset - 1];
		if (opc != AMD64_CALL && opc != AMD64_JMP32)
			errx(1, "unexpected opcode 0x%x for %s at offset 0x%lx",
			    opc, symname, offset);
		if (target[offset + 0] != 0 ||
		    target[offset + 1] != 0 ||
		    target[offset + 2] != 0 ||
		    target[offset + 3] != 0)
			errx(1, "unexpected addr for %s at offset 0x%lx",
			    symname, offset);

		/* Overwrite the call with NOPs. */
		memset(&target[offset - 1], AMD64_NOP, 5);

		/* If this was a tail call, we need to return instead. */
		if (opc == AMD64_JMP32)
			target[offset - 1] = AMD64_RETQ;

		/* Make sure the linker ignores this relocation. */
		*info &= ~GELF_R_TYPE(*info);
		*info |= R_X86_64_NONE;
		break;
	default:
		errx(1, "unhandled machine type 0x%x", ehdr->e_machine);
	}

	LOG("updated relocation for %s at 0x%lx", symname, offset - 1);

	inst = xmalloc(sizeof(*inst));
	inst->symname = symname;
	inst->offset = offset;

	SLIST_INSERT_HEAD(plist, inst, next);

	return (0);
}

/*
 * Look for relocations against DTrace probe stubs. Such relocations are used to
 * populate the probe instance list (plist) and then invalidated, since we
 * overwrite the call site with NOPs.
 */
static void
process_reloc_section(Elf *e, GElf_Ehdr *ehdr, GElf_Shdr *shdr, Elf_Scn *scn,
    struct probe_list *plist)
{
	GElf_Shdr symshdr;
	GElf_Rel rel;
	GElf_Rela rela;
	Elf_Data *reldata, *targdata;
	Elf_Scn *symscn, *targscn;
	const char *name;
	u_int i;
	int ret;

	if ((targscn = elf_getscn(e, shdr->sh_info)) == NULL)
		errx(1, "failed to look up relocation section: %s", ELF_ERR());
	if ((targdata = elf_getdata(targscn, NULL)) == NULL)
		errx(1, "failed to look up target section data: %s", ELF_ERR());

	/* We only want to process relocations against the text section. */
	name = get_section_name(e, targscn);
	if (strcmp(name, ".text") != 0) {
		LOG("skipping relocation section for %s", name);
		return;
	}

	if ((symscn = elf_getscn(e, shdr->sh_link)) == NULL)
		errx(1, "failed to look up symbol table: %s", ELF_ERR());
	if (gelf_getshdr(symscn, &symshdr) == NULL)
		errx(1, "failed to look up symbol table header: %s", ELF_ERR());

	i = 0;
	for (reldata = NULL; (reldata = elf_getdata(scn, reldata)) != NULL; ) {
		for (; i < shdr->sh_size / shdr->sh_entsize; i++) {
			if (shdr->sh_type == SHT_REL) {
				if (gelf_getrel(reldata, i, &rel) == NULL)
					errx(1, "gelf_getrel: %s", ELF_ERR());
				ret = process_reloc(e, ehdr, &symshdr, symscn,
				    targdata->d_buf, rel.r_offset, &rel.r_info,
				    plist);
				if (ret == 0 &&
				    gelf_update_rel(reldata, i, &rel) == 0)
					errx(1, "gelf_update_rel: %s",
					    ELF_ERR());
			} else {
				assert(shdr->sh_type == SHT_RELA);
				if (gelf_getrela(reldata, i, &rela) == NULL)
					errx(1, "gelf_getrela: %s", ELF_ERR());
				ret = process_reloc(e, ehdr, &symshdr, symscn,
				    targdata->d_buf, rela.r_offset,
				    &rela.r_info, plist);
				if (ret == 0 &&
				    gelf_update_rela(reldata, i, &rela) == 0)
					errx(1, "gelf_update_rela: %s",
					    ELF_ERR());
			}

			/*
			 * We've updated the relocation and the corresponding
			 * text section.
			 */
			if (ret == 0) {
				if (elf_flagdata(targdata, ELF_C_SET,
				    ELF_F_DIRTY) == 0)
					errx(1, "elf_flagdata: %s", ELF_ERR());
				if (elf_flagdata(reldata, ELF_C_SET,
				    ELF_F_DIRTY) == 0)
					errx(1, "elf_flagdata: %s", ELF_ERR());
			}
		}
	}
}

/*
 * Process an input object file. This function choreographs the work done by
 * sdtconvert: it first processes all the relocations against the DTrace probe
 * stubs and uses the information from those relocations to build up a list
 * (plist) of probe sites. It then adds information about each probe site to the
 * object file, used by the kernel SDT module to actually create DTrace probes.
 */
static void
process_obj(const char *obj)
{
	struct probe_list plist;
	GElf_Ehdr ehdr;
	GElf_Shdr shdr;
	struct probe_instance *inst, *tmp;
	Elf_Scn *scn, *datarelscn, *instscn, *instrelscn, *datascn, *symscn;
	Elf *e;
	char *objpath;
	int fd, cnt, ndx;

	if ((fd = open(obj, O_RDWR)) < 0)
		err(1, "failed to open %s", obj);

	if ((e = elf_begin(fd, ELF_C_RDWR, NULL)) == NULL)
		errx(1, "elf_begin: %s", ELF_ERR());

	if (gelf_getehdr(e, &ehdr) == NULL)
		errx(1, "gelf_getehdr: %s", ELF_ERR());
	if (ehdr.e_type != ET_REL) {
		warnx("invalid ELF type for '%s'", obj);
		return;
	}

	SLIST_INIT(&plist);

	/* Hijack relocations for DTrace probe stub calls. */

	for (scn = NULL; (scn = elf_nextscn(e, scn)) != NULL; ) {
		if (gelf_getshdr(scn, &shdr) == NULL)
			errx(1, "gelf_getshdr: %s", ELF_ERR());

		if (shdr.sh_type == SHT_REL || shdr.sh_type == SHT_RELA)
			process_reloc_section(e, &ehdr, &shdr, scn, &plist);
	}

	if (SLIST_EMPTY(&plist)) {
		/* No probe instances in this object file, we're done. */
		LOG("no probes found in %s", obj);
		return;
	}

	/* Now record all of the instance sites. */

	/* XXX this isn't the right way to find these sections. */
	if ((symscn = section_by_name(e, ".symtab")) == NULL)
		errx(1, "couldn't find symbol table in %s", obj);
	if ((datascn = section_by_name(e, ".data")) == NULL)
		errx(1, "couldn't find data section in %s", obj);
	if ((datarelscn = get_reloc_section(e, datascn)) == NULL) {
		/*
		 * The object file doesn't have any relocations against the data
		 * section, so we have to create a relocation section ourselves.
		 */
		LOG("adding data relocation section for %s", obj);
		datarelscn = add_reloc_section(e, datascn, symscn);
	}

	cnt = 0;
	SLIST_FOREACH(inst, &plist, next)
	    cnt++;
	init_new_sections(e, symscn, &instscn, &instrelscn, cnt * wordsize(e));

	if ((objpath = realpath(obj, NULL)) == NULL)
		errx(1, "failed to resolve %s: %s", obj, strerror(errno));

	ndx = 0;
	SLIST_FOREACH_SAFE(inst, &plist, next, tmp) {
		record_instance(e, &ehdr, symscn, datascn, datarelscn,
		    instrelscn, inst, ndx++, objpath);
		SLIST_REMOVE(&plist, inst, probe_instance, next);
		free(inst);
	}

	if (elf_update(e, ELF_C_WRITE) == -1)
		errx(1, "elf_update: %s", ELF_ERR());

	(void)elf_end(e);
	(void)close(fd);
}

/*
 * Add a probe instance to the target ELF file. This consists of several steps:
 * - add space for a struct sdt_instance to the data section,
 * - add a symbol table entry for the instance,
 * - add a relocation for the probe field of the struct sdt_instance,
 * - add a relocation for the probe instance linker set.
 */
static void
record_instance(Elf *e, GElf_Ehdr *ehdr, Elf_Scn *symscn, Elf_Scn *datascn,
    Elf_Scn *datarelscn, Elf_Scn *instrelscn, const struct probe_instance *inst,
    int ndx, const char *objpath)
{
	struct sdt_instance sdtinst;
	Elf64_Rela rela;
	Elf64_Sym sym64;
	Elf32_Sym sym32;
	GElf_Sym probeobjsym;
	GElf_Shdr symshdr;
	Elf_Scn *strscn;
	char *probeobjname, *instsymname;
	void *sym;
	size_t instoff, nameoff, namesz, relsz, symsz;
	uint64_t probeobjndx, instndx;

	sdtinst.probe = NULL; /* Filled in with the relocation from step 3. */
	sdtinst.offset = inst->offset;

	/*
	 * Step 1: install the probe instance into the data section.
	 */

	instoff = append_data(e, datascn, &sdtinst, sizeof(sdtinst));
	LOG("created probe instance for '%s' at offset %zu", inst->symname,
	    instoff);

	/*
	 * Step 2: add a symbol table entry for the probe instance object.
	 */

	/*
	 * Step 2.1: create a unique name for the symbol and add it to the
	 * string table.
	 */
	asprintf(&instsymname, "%s%d.%ld", sdtinst_prefix, ndx,
	    ftok(objpath, 0));
	if (instsymname == NULL)
		errx(1, "asprintf: %s", strerror(errno));

	if (gelf_getshdr(symscn, &symshdr) != &symshdr)
		errx(1, "failed to look up section header for %s: %s",
		    get_section_name(e, symscn), ELF_ERR());
	if ((strscn = elf_getscn(e, symshdr.sh_link)) == NULL)
		errx(1, "failed to find string table for %s: %s",
		    get_section_name(e, symscn), ELF_ERR());
	nameoff = append_data(e, strscn, instsymname, strlen(instsymname) + 1);

	/*
	 * Step 2.2: create the symbol table entry and add it to the table.
	 */
	switch (gelf_getclass(e)) {
	case ELFCLASS32:
		sym32.st_name = nameoff;
		sym32.st_value = instoff;
		sym32.st_size = sizeof(sdtinst); /* XXX cross-compat... */
		sym32.st_info = ELF32_ST_INFO(STB_GLOBAL, STT_OBJECT);
		sym32.st_other = 0;
		sym32.st_shndx = elf_ndxscn(datascn);

		symsz = sizeof(sym32);
		sym = &sym32;
		break;
	case ELFCLASS64:
		sym64.st_name = nameoff;
		sym64.st_info = ELF64_ST_INFO(STB_GLOBAL, STT_OBJECT);
		sym64.st_other = 0;
		sym64.st_shndx = elf_ndxscn(datascn);
		sym64.st_value = instoff;
		sym64.st_size = sizeof(sdtinst); /* XXX cross-compat... */

		symsz = sizeof(sym64);
		sym = &sym64;
		break;
	default:
		errx(1, "unexpected ELF class %d", gelf_getclass(e));
	}

	instndx = append_data(e, symscn, sym, symsz) / symsz;

	LOG("added symbol table entry for '%s' at index %ju", inst->symname,
	    (uintmax_t)instndx);

	/*
	 * Step 3: add a relocation for the object we added in step 2. We need
	 * to ensure that the instance's probe pointer is set to the
	 * corresponding struct sdt_probe.
	 */

	/*
	 * If the probe name is "__dtrace_probe_<foo>", the probe object name is
	 * "sdt_<foo>".
	 */
	namesz = strlen(sdtobj_prefix) + strlen(inst->symname) -
	    strlen(probe_prefix) + 1;
	probeobjname = xmalloc(namesz);
	(void)strlcpy(probeobjname, sdtobj_prefix, namesz);
	(void)strlcat(probeobjname, inst->symname + strlen(probe_prefix),
	    namesz);

	if (symbol_by_name(e, symscn, probeobjname, &probeobjsym,
	    &probeobjndx) == 0)
		errx(1, "couldn't find probe object '%s'", probeobjname);
	free(probeobjname);

	switch (ehdr->e_machine) {
	case EM_X86_64:
		rela.r_offset = instoff; /* probe pointer is the first field */
		rela.r_info = ELF64_R_INFO(probeobjndx, R_X86_64_64);
		rela.r_addend = 0;

		relsz = sizeof(rela);
		break;
	default:
		errx(1, "unhandled machine type 0x%x", ehdr->e_machine);
	}

	append_data(e, datarelscn, &rela, relsz);

	/*
	 * Step 4: add a relocation for the new probe instance object (created
	 * in step 1) to the probe instance linker set.
	 */

	switch (ehdr->e_machine) {
	case EM_X86_64:
		rela.r_offset = ndx * wordsize(e);
		rela.r_info = ELF64_R_INFO(instndx, R_X86_64_64);
		rela.r_addend = 0;

		relsz = sizeof(rela);
		break;
	default:
		errx(1, "unhandled machine type 0x%x", ehdr->e_machine);
	}

	append_data(e, instrelscn, &rela, relsz);

	/* Fin. */
}

/* Look up an ELF section by name. */
static Elf_Scn *
section_by_name(Elf *e, const char *name)
{
	Elf_Scn *scn;

	for (scn = NULL; (scn = elf_nextscn(e, scn)) != NULL; )
		if (strcmp(get_section_name(e, scn), name) == 0)
			return (scn);
	return (NULL);
}

/*
 * Look up a symbol by name from the specified symbol table. Return 1 if a
 * matching symbol was found, 0 otherwise.
 */
static int
symbol_by_name(Elf *e, Elf_Scn *scn, const char *symname, GElf_Sym *sym,
    uint64_t *ndx)
{
	GElf_Shdr shdr;
	Elf_Data *data;
	const char *name;
	u_int i;

	if (gelf_getshdr(scn, &shdr) != &shdr)
		errx(1, "gelf_getshdr: %s", ELF_ERR());

	i = 0;
	for (data = NULL; (data = elf_getdata(scn, NULL)) != NULL; ) {
		for (; i < shdr.sh_size / shdr.sh_entsize; i++) {
			if (gelf_getsym(data, i, sym) == NULL)
				errx(1, "gelf_getsym: %s", ELF_ERR());
			name = elf_strptr(e, shdr.sh_link, sym->st_name);
			if (name != NULL && strcmp(name, symname) == 0) {
				*ndx = i;
				return (1); /* There's my chippy. */
			}
		}
	}
	return (0);
}

/*
 * Retrieve the symbol at index ndx in the specified symbol table, with bounds
 * checking.
 */
static GElf_Sym *
symbol_by_index(Elf_Scn *symtab, int ndx)
{
	Elf_Data *symdata;

	if ((symdata = elf_getdata(symtab, NULL)) == NULL)
		errx(1, "couldn't find symbol table data: %s", ELF_ERR());
	if (symdata->d_size < (ndx + 1) * sizeof(GElf_Sym))
		errx(1, "invalid symbol index %d", ndx);
	return (&((GElf_Sym *)symdata->d_buf)[ndx]);
}

static int
wordsize(Elf *e)
{
	int class;

	if ((class = gelf_getclass(e)) == ELFCLASSNONE)
		errx(1, "gelf_getclass() returned ELFCLASSNONE");
	else if (class != ELFCLASS32 && class != ELFCLASS64)
		errx(1, "gelf_getclass() returned unexpected class %d", class);
	return (class == ELFCLASS32 ? 4 : 8);
}

static void *
xmalloc(size_t n)
{
	void *ret;

	if ((ret = malloc(n)) == NULL)
		errx(1, "malloc");
	return (ret);
}

static void
usage(void)
{

	fprintf(stderr, "%s: [-v] <obj> [<obj> ...]\n", getprogname());
	exit(1);
}

int
main(int argc, char **argv)
{

	if (argc > 1 && strcmp(argv[1], "-v") == 0) {
		verbose = true;
		argv++; argc--;
	}

	if (argc <= 1)
		usage();

	if (elf_version(EV_CURRENT) == EV_NONE)
		errx(1, "ELF library too old");

	for (int i = 1; i < argc; i++)
		process_obj(argv[i]);

	return (0);
}
