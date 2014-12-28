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

#include <assert.h>
#include <err.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <gelf.h>
#include <libelf.h>

#define	AMD64_CALL	0xe8
#define	AMD64_JMP32	0xe9
#define	AMD64_NOP	0x90
#define	AMD64_RETQ	0xc3

static GElf_Sym	*symlookup(Elf_Data *, int);
static int	process_rel(Elf *, GElf_Ehdr *, GElf_Shdr *, Elf_Data *,
		    uint8_t *, GElf_Addr, GElf_Xword *);
static void	process_reloc_scn(Elf *, GElf_Ehdr *, GElf_Shdr *, Elf_Scn *);
static void	process_obj(const char *);
static void	usage(void);

static const char probe_prefix[] = "__dtrace_probe_";

static GElf_Sym *
symlookup(Elf_Data *symtab, int ndx)
{

	if (symtab->d_size < (ndx + 1) * sizeof(GElf_Sym))
		errx(1, "invalid symbol index %d", ndx);
	return (&((GElf_Sym *)symtab->d_buf)[ndx]);
}

/* XXX need obj filename for better error messages. */
/* XXX need to compose consecutive relocations. */
static int
process_rel(Elf *e, GElf_Ehdr *ehdr, GElf_Shdr *symhdr, Elf_Data *symtab,
    uint8_t *target, GElf_Addr offset, GElf_Xword *info)
{
	GElf_Sym *sym;
	char *symname;
	uint8_t opc;

	sym = symlookup(symtab, GELF_R_SYM(*info));
	symname = elf_strptr(e, symhdr->sh_link, sym->st_name);
	if (symname == NULL)
		errx(1, "elf_strptr: %s", elf_errmsg(elf_errno()));

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
		/* XXX sanity check on the relocation type? */
#if 0
		switch (GELF_R_TYPE(info)) {
		case R_X86_64_64:
		case R_X86_64_PC32:
			break;
		default:
			errx(1, "unhandled relocation type %lu for %s",
			    GELF_R_TYPE(info), symname);
		}
#endif
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

	return (0);
}

static void
process_reloc_scn(Elf *e, GElf_Ehdr *ehdr, GElf_Shdr *shdr, Elf_Scn *scn)
{
	GElf_Shdr symhdr;
	GElf_Rel rel;
	GElf_Rela rela;
	Elf_Data *data, *symdata, *targdata;
	Elf_Scn *symscn, *targ;
	u_int i;
	int ret;

	targ = elf_getscn(e, shdr->sh_info);
	if (targ == NULL)
		errx(1, "failed to look up relocation section: %s",
		    elf_errmsg(elf_errno()));
	/* XXX multiple descriptors */
	targdata = elf_getdata(targ, NULL);
	if (targdata == NULL)
		errx(1, "failed to look up target section data: %s",
		    elf_errmsg(elf_errno()));

	symscn = elf_getscn(e, shdr->sh_link);
	if (symscn == NULL)
		errx(1, "failed to look up symbol table: %s",
		    elf_errmsg(elf_errno()));
	if (gelf_getshdr(symscn, &symhdr) == NULL)
		errx(1, "failed to look up symbol table header: %s",
		    elf_errmsg(elf_errno()));

	/* XXX handle multiple data descriptors */
	symdata = elf_getdata(symscn, NULL);
	if (symdata == NULL)
		errx(1, "elf_getdata: %s", elf_errmsg(elf_errno()));

	i = 0;
	data = NULL;
	while ((data = elf_getdata(scn, data)) != NULL) {
		for (; i < shdr->sh_size / shdr->sh_entsize; i++) {
			if (shdr->sh_type == SHT_REL) {
				if (gelf_getrel(data, i, &rel) == NULL)
					errx(1, "gelf_getrel: %s",
					    elf_errmsg(elf_errno()));
				ret = process_rel(e, ehdr, &symhdr, symdata,
				    targdata->d_buf, rel.r_offset, &rel.r_info);
				if (ret == 0 &&
				    gelf_update_rel(data, i, &rel) == 0)
					errx(1, "gelf_update_rel: %s",
					    elf_errmsg(elf_errno()));
			} else {
				assert(shdr->sh_type == SHT_RELA);
				if (gelf_getrela(data, i, &rela) == NULL)
					errx(1, "gelf_getrela: %s",
					    elf_errmsg(elf_errno()));
				ret = process_rel(e, ehdr, &symhdr, symdata,
				    targdata->d_buf, rela.r_offset,
				    &rela.r_info);
				if (ret == 0 &&
				    gelf_update_rela(data, i, &rela) == 0)
					errx(1, "gelf_update_rela: %s",
					    elf_errmsg(elf_errno()));
			}
		}
	}
}

static void
process_obj(const char *obj)
{
	GElf_Ehdr ehdr;
	GElf_Shdr shdr;
	Elf_Scn *scn;
	Elf *e;
	int fd;

	fd = open(obj, O_RDWR);
	if (fd < 0)
		err(1, "failed to open %s", obj);

	e = elf_begin(fd, ELF_C_RDWR, NULL);
	if (e == NULL)
		errx(1, "elf_begin: %s", elf_errmsg(elf_errno()));

	if (gelf_getehdr(e, &ehdr) == NULL)
		errx(1, "gelf_getehdr: %s", elf_errmsg(elf_errno()));
	if (ehdr.e_type != ET_REL) {
		warnx("invalid ELF type for '%s'", obj);
		return;
	}

	scn = NULL;
	while ((scn = elf_nextscn(e, scn)) != NULL) {
		if (gelf_getshdr(scn, &shdr) == NULL)
			errx(1, "gelf_getshdr: %s", elf_errmsg(elf_errno()));

		if (shdr.sh_type == SHT_REL || shdr.sh_type == SHT_RELA)
			process_reloc_scn(e, &ehdr, &shdr, scn);
	}

	if (elf_update(e, ELF_C_WRITE) == -1)
		errx(1, "elf_update: %s", elf_errmsg(elf_errno()));

	(void)elf_end(e);
	(void)close(fd);
}

static void
usage(void)
{

	fprintf(stderr, "%s: <obj> [<obj> ...]\n", getprogname());
	exit(1);
}

int
main(int argc, char **argv)
{

	if (argc <= 1)
		usage();

	if (elf_version(EV_CURRENT) == EV_NONE)
		errx(1, "ELF library too old");

	for (int i = 1; i < argc; i++)
		process_obj(argv[i]);

	return (0);
}
