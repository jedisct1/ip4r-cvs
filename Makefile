
MODULES = ip4r
DATA_built = ip4r.sql
DOCS = README.ip4r

PG_CONFIG = pg_config
PG_CPPFLAGS = -DIP4R_PGVER=$(shell echo $(VERSION) | awk -F. '{ print ($$1*1000+$$2)*1000+$$3 }')
PGXS = $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
