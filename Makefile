
MODULE_big = ip4r
DATA_built = ip4r.sql
DOCS = README.ip4r
OBJS = ip4r.o ip6r.o ipaddr.o iprange.o raw_io.o

ifndef NO_PGXS
PG_CONFIG = pg_config
PG_CPPFLAGS = -DIP4R_PGVER=$(shell echo $(VERSION) | awk -F. '{ print ($$1*1000+$$2)*1000+$$3 }')
PGXS = $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/ip4r
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
CFLAGS += -DIP4R_PGVER=$(shell echo $(VERSION) | awk -F. '{ print ($$1*1000+$$2)*1000+$$3 }')
include $(top_srcdir)/contrib/contrib-global.mk
endif

