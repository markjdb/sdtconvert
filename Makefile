# $FreeBSD$

PROG=	sdtconvert
BINDIR?= /usr/bin
MAN=

LDADD=	-lelf

.include <bsd.prog.mk>
