clean:
	#!/usr/bin/env bash
	pushd LF
	make clean
	rm -f *.glob
	rm -f *.vo
	rm -f *.vok
	rm -f *.vos
	rm -f .*.aux
	rm -f .*.d
	rm -f Makefile*
	rm -f .lia.cache
	rm -f *.ml*
	popd

build:
	#!/usr/bin/env bash
	pushd LF
	make
	popd

fullbuild:
	#!/usr/bin/env bash
	pushd LF
	coq_makefile -f _CoqProject *.v -o Makefile
	make clean
	make
	popd
