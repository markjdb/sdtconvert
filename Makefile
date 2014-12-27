# $FreeBSD$

PROG=	sdtconvert
BINDIR?= /usr/bin
MAN=

LDADD=	-lelf

WARNS?=	6

.include <bsd.prog.mk>
