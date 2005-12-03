
MODULES = ip4r
DATA_built = ip4r.sql
#DOCS = README.ip4r

ifdef USE_PGXS
PG_CPPFLAGS = -DMAJOR_VERSION=$(shell echo $(VERSION) | sed 's/\..*//')
PGXS = $(shell pg_config --pgxs)
include $(PGXS)
else
subdir = contrib/ip4r
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
CFLAGS += -DMAJOR_VERSION=$(shell echo $(VERSION) | sed 's/\..*//')
include $(top_srcdir)/contrib/contrib-global.mk
endif

