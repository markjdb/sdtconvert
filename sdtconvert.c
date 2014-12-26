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

#include <err.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <libelf.h>
#include <gelf.h>

const char probe_prefix[] = "__dtrace_probe_";

static void
process_sym(Elf *e, GElf_Shdr *shdr, Elf_Data *data, int ndx, GElf_Sym *sym)
{
	const char *symname;

	symname = elf_strptr(e, shdr->sh_link, sym->st_name);

	if (strncmp(symname, probe_prefix, sizeof(probe_prefix) - 1) != 0)
		return;

	if (sym->st_shndx != SHN_UNDEF)
		return;

	sym->st_other &= GELF_ST_VISIBILITY(0);
	sym->st_other |= GELF_ST_VISIBILITY(STV_ELIMINATE);
	sym->st_shndx = SHN_ABS;

	if (gelf_update_sym(data, ndx, sym) == 0)
		errx(1, "gelf_update_sym: updating %s: %s", symname,
		    elf_errmsg(elf_errno()));
}

static void
process_obj(const char *obj)
{
	GElf_Ehdr ehdr;
	GElf_Shdr shdr;
	GElf_Sym sym;
	Elf_Data *data;
	Elf_Scn *scn;
	Elf *e;
	int fd, i;

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

		if (shdr.sh_type != SHT_DYNSYM && shdr.sh_type != SHT_SYMTAB)
			continue;

		data = NULL;
		while ((data = elf_getdata(scn, data)) != NULL) {
			for (i = 0; i < shdr.sh_size / shdr.sh_entsize; i++) {
				if (gelf_getsym(data, i, &sym) == NULL)
					errx(1, "gelf_getsym: %s",
					    elf_errmsg(elf_errno()));
				process_sym(e, &shdr, data, i, &sym);
			}
		}
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
