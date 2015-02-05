# $FreeBSD$

PROG=	sdtpatch
BINDIR?= /usr/bin
MAN=

LDADD=	-lelf

WARNS?=	6

.include <bsd.prog.mk>
