/*-
 * Copyright (c) 2014 Mark Johnston <markj@FreeBSD.org>
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

#include <sys/sdt.h>
#include <sys/queue.h>

#include <assert.h>
#include <err.h>
#include <fcntl.h>
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

static bool verbose = false;

struct probe_instance {
	const char	*symname;
	uint64_t	offset;
	SLIST_ENTRY(probe_instance) next;
};

SLIST_HEAD(probe_list, probe_instance);

static Elf_Scn	*add_section(Elf *, const char *);
static GElf_Sym	*symlookup(Elf_Data *, int);
static int	process_rel(Elf *, GElf_Ehdr *, GElf_Shdr *, Elf_Data *,
		    uint8_t *, GElf_Addr, GElf_Xword *, struct probe_list *);
static void	process_reloc_scn(Elf *, GElf_Ehdr *, GElf_Shdr *, Elf_Scn *,
		    struct probe_list *);
static void	process_obj(const char *);
static void	record_instance(Elf *, Elf_Scn *, Elf_Scn *,
		    struct probe_instance *);
static void	usage(void);
static void *	xmalloc(size_t);

static GElf_Sym *
symlookup(Elf_Data *symtab, int ndx)
{

	if (symtab->d_size < (ndx + 1) * sizeof(GElf_Sym))
		errx(1, "invalid symbol index %d", ndx);
	return (&((GElf_Sym *)symtab->d_buf)[ndx]);
}

static void *
xmalloc(size_t n)
{
	void *ret;

	ret = malloc(n);
	if (ret == NULL)
		errx(1, "malloc");
	return (ret);
}

/* XXX need obj filename for better error messages. */
static int
process_rel(Elf *e, GElf_Ehdr *ehdr, GElf_Shdr *symhdr, Elf_Data *symtab,
    uint8_t *target, GElf_Addr offset, GElf_Xword *info,
    struct probe_list *plist)
{
	struct probe_instance *inst;
	GElf_Sym *sym;
	char *symname;
	uint8_t opc;

	sym = symlookup(symtab, GELF_R_SYM(*info));
	symname = elf_strptr(e, symhdr->sh_link, sym->st_name);
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

	/* XXX only want to update text... */

	switch (ehdr->e_machine) {
	case EM_X86_64:
		switch (GELF_R_TYPE(*info)) {
		case R_X86_64_64:
		case R_X86_64_PC32:
			break;
		default:
			errx(1, "unexpected relocation type %lu for %s",
			    GELF_R_TYPE(*info), symname);
		}

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

		/*
		 * Set the relocation type to R_X86_64_NONE so that the linker
		 * ignores it.
		 */
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

static void
process_reloc_scn(Elf *e, GElf_Ehdr *ehdr, GElf_Shdr *shdr, Elf_Scn *scn,
    struct probe_list *plist)
{
	GElf_Shdr symhdr;
	GElf_Rel rel;
	GElf_Rela rela;
	Elf_Data *reldata, *symdata, *targdata;
	Elf_Scn *symscn, *targ;
	u_int i;
	int ret;

	targ = elf_getscn(e, shdr->sh_info);
	if (targ == NULL)
		errx(1, "failed to look up relocation section: %s", ELF_ERR());
	targdata = elf_getdata(targ, NULL);
	if (targdata == NULL)
		errx(1, "failed to look up target section data: %s", ELF_ERR());

	symscn = elf_getscn(e, shdr->sh_link);
	if (symscn == NULL)
		errx(1, "failed to look up symbol table: %s", ELF_ERR());
	if (gelf_getshdr(symscn, &symhdr) == NULL)
		errx(1, "failed to look up symbol table header: %s", ELF_ERR());

	symdata = elf_getdata(symscn, NULL);
	if (symdata == NULL)
		errx(1, "elf_getdata: %s", ELF_ERR());

	i = 0;
	reldata = NULL;
	while ((reldata = elf_getdata(scn, reldata)) != NULL) {
		for (; i < shdr->sh_size / shdr->sh_entsize; i++) {
			if (shdr->sh_type == SHT_REL) {
				if (gelf_getrel(reldata, i, &rel) == NULL)
					errx(1, "gelf_getrel: %s", ELF_ERR());
				ret = process_rel(e, ehdr, &symhdr, symdata,
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
				ret = process_rel(e, ehdr, &symhdr, symdata,
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

static Elf_Scn *
add_section(Elf *e, const char *name)
{
	GElf_Shdr newshdr, strshdr;
	Elf_Data *strdata, *newstrdata;
	Elf_Scn *newscn, *strscn;
	size_t len, shdrstrndx;

	/* First add the section name to the section header string table. */
	if (elf_getshdrstrndx(e, &shdrstrndx) != 0)
		errx(1, "elf_getshdrstrndx: %s", ELF_ERR());
	if ((strscn = elf_getscn(e, shdrstrndx)) == NULL)
		errx(1, "elf_getscn on shdrstrtab: %s", ELF_ERR());
	if (gelf_getshdr(strscn, &strshdr) != &strshdr)
		errx(1, "gelf_getshdr on shdrstrtab: %s", ELF_ERR());
	if ((strdata = elf_getdata(strscn, NULL)) == NULL)
		errx(1, "elf_getdata on shdrstrtab: %s", ELF_ERR());
	if ((newstrdata = elf_newdata(strscn)) == NULL)
		errx(1, "elf_newdata on shdrstrtab: %s", ELF_ERR());

	len = strlen(name) + 1;
	newstrdata->d_align = strdata->d_align;
	newstrdata->d_buf = xmalloc(len);
	memcpy(newstrdata->d_buf, name, len);
	newstrdata->d_size = len;
	newstrdata->d_type = strdata->d_type;
	newstrdata->d_version = elf_version(EV_CURRENT);

	strshdr.sh_size += len;

	/* Then create the actual section. */
	if ((newscn = elf_newscn(e)) == NULL)
		errx(1, "elf_newscn: %s", ELF_ERR());
	if (gelf_getshdr(newscn, &newshdr) != &newshdr)
		errx(1, "gelf_getshdr: %s", ELF_ERR());

	newshdr.sh_name = strshdr.sh_size - len;
	newshdr.sh_type = SHT_PROGBITS;
	newshdr.sh_flags = SHF_ALLOC;
	newshdr.sh_addralign = 8;

	if (gelf_update_shdr(newscn, &newshdr) == 0)
		errx(1, "gelf_update_shdr: %s", ELF_ERR());
	if (gelf_update_shdr(strscn, &strshdr) == 0)
		errx(1, "gelf_update_shdr: %s", ELF_ERR());

	LOG("added section %s", name);

	return (newscn);
}

static void
process_obj(const char *obj)
{
	struct probe_list plist;
	GElf_Ehdr ehdr;
	GElf_Shdr shdr;
	struct probe_instance *inst, *tmp;
	Elf_Scn *scn, *instscn, *instrelscn;
	Elf *e;
	int fd;

	fd = open(obj, O_RDWR);
	if (fd < 0)
		err(1, "failed to open %s", obj);

	e = elf_begin(fd, ELF_C_RDWR, NULL);
	if (e == NULL)
		errx(1, "elf_begin: %s", ELF_ERR());

	if (gelf_getehdr(e, &ehdr) == NULL)
		errx(1, "gelf_getehdr: %s", ELF_ERR());
	if (ehdr.e_type != ET_REL) {
		warnx("invalid ELF type for '%s'", obj);
		return;
	}

	SLIST_INIT(&plist);

	/* Perform relocations for DTrace probe stub calls. */
	scn = NULL;
	while ((scn = elf_nextscn(e, scn)) != NULL) {
		if (gelf_getshdr(scn, &shdr) == NULL)
			errx(1, "gelf_getshdr: %s", ELF_ERR());

		if (shdr.sh_type == SHT_REL || shdr.sh_type == SHT_RELA)
			process_reloc_scn(e, &ehdr, &shdr, scn, &plist);
	}

	/* No SDT probes in this object file. */
	if (SLIST_EMPTY(&plist)) {
		LOG("no probes found in %s", obj);
		return;
	}

	instscn = add_section(e, "set_sdt_instance_set");
	instrelscn = add_section(e, ".relaset_sdt_instance_set");

	SLIST_FOREACH_SAFE(inst, &plist, next, tmp) {
		record_instance(e, instscn, instrelscn, inst);
		SLIST_REMOVE(&plist, inst, probe_instance, next);
		free(inst);
	}

	if (elf_update(e, ELF_C_WRITE) == -1)
		errx(1, "elf_update: %s", ELF_ERR());

	(void)elf_end(e);
	(void)close(fd);
}

static void
record_instance(Elf *e __unused, Elf_Scn *instscn, Elf_Scn *instrelscn __unused,
    struct probe_instance *inst)
{
	struct sdt_instance sdtinst;
	Elf_Data *data;
	size_t sz;

	if ((data = elf_newdata(instscn)) == NULL)
		errx(1, "elf_newdata: %s", ELF_ERR());

	sz = sizeof(sdtinst);
	sdtinst.probe = NULL; /* Filled in with a relocation. */
	sdtinst.offset = inst->offset;

	data->d_align = 1;
	data->d_buf = xmalloc(sz);
	memcpy(data->d_buf, &sdtinst, sz);
	data->d_size = sz;
	data->d_type = ELF_T_BYTE;
	data->d_version = elf_version(EV_CURRENT);
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
