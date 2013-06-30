.PHONY: echoes clean lint lint-nocolor   #  let ghc --make handle the dependencies.

OBJECT_DIR=output
INTERFACE_DIR=output
SOURCE_DIR=src
OPT_LEVEL=-O2
COMPILE_OPTIONS=-Wall -Werror

echoes:
	mkdir -p ${INTERFACE_DIR}
	mkdir -p ${OBJECT_DIR}
	ghc ${OPT_LEVEL} ${COMPILE_OPTIONS} -hidir ${INTERFACE_DIR} 		\
	-odir ${OBJECT_DIR} -i${SOURCE_DIR} --make ${SOURCE_DIR}/Main.hs	\
	-o echoes

clean:
	rm -f echoes
	rm -rf ${INTERFACE_DIR}
	rm -rf ${OBJECT_DIR}

lint:
	find . -name '*hs' | xargs hlint --color

lint-nocolor:
	find . -name '*hs' | xargs hlint
