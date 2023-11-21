# Updated with some ideas from <https://github.com/coq-community/manifesto/wiki/Project-build-scripts>

.PHONY: all clean

SOURCES:=$(shell find . -name '*.v')
MCOQ:=Makefile.coq

all: $(MCOQ)
	+$(MAKE) -f $< all

clean: $(MCOQ)
	+$(MAKE) -f $< cleanall
	rm -f Makefile.coq Makefile.coq.conf

$(MCOQ): _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@ $(SOURCES)

_CoqProject: . Makefile
	echo '-Q . Whiskey' > $@
