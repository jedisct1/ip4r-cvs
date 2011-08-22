
MODULE_big = ip4r
DATA_built = ip4r.sql
DOCS = README.ip4r
OBJS = ip4r_module.o ip4r.o ip6r.o ipaddr.o iprange.o raw_io.o
REGRESS = ip4r

ifndef NO_PGXS
PG_CONFIG = pg_config
PGXS = $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/ip4r
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif

