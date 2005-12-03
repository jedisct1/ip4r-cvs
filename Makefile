subdir = contrib/ip4r
top_builddir = ../..
include $(top_builddir)/src/Makefile.global


MODULE_big = ip4r
OBJS = ip4r.o
DATA_built = ip4r.sql
CFLAGS += -DMAJOR_VERSION=$(shell echo $(VERSION) | sed 's/\..*//')

ip4r.o: ip4r.c

include $(top_srcdir)/contrib/contrib-global.mk
