TARGETS=HanoiCmdLine.exe

GENERATE_DATA := python2 generate-data.py
GENERATE_GRAPHS := python2 transform-data.py
CREATE_DEFAULT_ANSWERS := python2 create-default-answers.py

.PHONY: all build clean %.exe

all: build link

build:
	dune build app/HanoiCmdLine.exe

link: $(TARGETS)

%.exe:
	if [ ! -f $@ ]; then ln -s _build/default/app/$@ . ; fi

install:
	jbuilder install

clean:
	rm -rf _build *.install *.pdf $(TARGETS)

documentation:
	jbuilder build @docs

generate-data: all
	$(GENERATE_DATA) ./HanoiCmdLine.exe benchmarks benchmarks-no-helper/vfa/tree_::_priqueue.ds benchmarks-no-helper/vfa/tree_::_priqueue+binfuncs.ds benchmarks/coq/bst_::_set.ds

generate-outs: all
	$(CREATE_DEFAULT_ANSWERS) ./HanoiCmdLine.exe benchmarks

generate-all: all
	$(GENERATE_DATA) ./HanoiCmdLine.exe benchmarks benchmarks-no-helper/vfa/tree_::_priqueue.ds benchmarks-no-helper/vfa/tree_::_priqueue+binfuncs.ds benchmarks/coq/bst_::_set.ds
	$(GENERATE_GRAPHS) generated_data/generated_data.csv

