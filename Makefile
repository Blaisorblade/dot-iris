# Call `make V=1` to be more verbose

ifeq ($(V),1)
E=@true
Q=
MFLAGS=
else
E=@echo
Q=@
MFLAGS=-s
endif

.PHONY: coq clean

COQSRC = $(filter-out %_orig.v,$(wildcard theories/*.v))

all:

%: Makefile.coq phony
	$(E) "  MAKE -f Makefile.coq $@"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq $@

Makefile.coq: Makefile $(VS)
	$(E) "  COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject $(COQSRC)  -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq clean
	$(Q)rm -f *.bak *.d *.glob *~

# Phony wildcard targets

phony: ;
.PHONY: phony

# Some files that do *not* need to be forwarded to Makefile.coq
# The final semicolon prevents the forwarding.
distclean: clean cleancoq ;

Makefile: ;

cleancoq: ;
	$(E) "  RM Makefile.coq"
	$(Q)rm -f Makefile.coq Makefile.coq.conf
recoq: cleancoq Makefile.coq ;
