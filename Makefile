# stack is very slow to realize that sometimes no work is necessary

NAME	=	nimzo
SrcDir	= 	compiler/

EXE	=	$$(stack path --local-install-root)/bin/$(NAME)-exe
SRC	:=	$(shell find $(SrcDir) -type f -name '*.hs')

all: $(NAME)
fast: $(SRC)
	stack -j9 ghci --no-build --ghc-options="-j -fbyte-code -dynamic +RTS -A128m -n2m -RTS"
prof:
	stack -j9 build --executable-profiling --library-profiling --ghc-options="-fprof-auto"

#mk prof && .stack-work/dist/x86_64-linux-nix/Cabal-2.4.0.1/build/nimzo-exe/nimzo-exe demo.nimzo -p llvm-hs +RTS -p -xc

$(NAME): $(SRC)
	stack -j9 build --fast --ghc-options="-dynamic" &&\
	ln -sf $(EXE) ./$(NAME)
	@touch $(NAME) # since stack does nothing if you modify a file without changing code
