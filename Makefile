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

COQSRC = $(filter-out %_orig.v,$(wildcard *.v))
coq: Makefile.coq
	$(E) "  MAKE Makefile.coq"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(E) "  COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject $(COQSRC)  -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq clean
	$(Q)rm -f *.bak *.d *.glob *~

distclean: clean
	$(Q)rm -f Makefile.coq Makefile.coq.conf
