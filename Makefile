COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments --utf8

export COQDOCFLAGS

######

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	@$(MAKE) -f Makefile.coq $@

all: Makefile.coq
	@$(MAKE) -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	@$(MAKE) -f Makefile.coq clean
	find theories tests \( -name "*.d" -o -name "*.vo" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq
.PHONY: clean

html: all
	rm -fr html-old
	[ -d html ] && mv html html-old || true
	@$(MAKE) -f Makefile.coq $@
.PHONY: html

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	@echo "COQ_MAKEFILE"
	@"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
opam: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
