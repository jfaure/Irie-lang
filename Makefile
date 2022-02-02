# stack is very slow to realize that sometimes no work is necessary
NAME	=	irie
SrcDir	= 	compiler/

EXE	=	$$(stack path --local-install-root)/bin/$(NAME)-exe
SRC	:=	$(shell find $(SrcDir) -type f -name '*.hs')

all: $(NAME)
fast: $(SRC)
#stack -j9 ghci --ghci-options "-interactive-print=Text.Pretty.Simple.pPrint" --system-ghc --no-build --ghc-options="-j -fbyte-code -dynamic +RTS -A128m -n2m -RTS"
	stack -j9 ghci --system-ghc --no-build --ghc-options="-j -fbyte-code -dynamic +RTS -A128m -n2m -RTS"
prof:
	stack -j9 build --system-ghc --executable-profiling --ghc-options="-fprof-auto -fprof-cafs -with-rtsopts=-xc"

xprof:
	stack -j9 build --ghc-options='-prof -fprof-auto -fprof-cafs -with-rtsopts=-xc'
# --library-profiling 

#mk prof && .stack-work/dist/x86_64-linux-nix/Cabal-3.2.1.0/build/irie-exe/irie-exe demo.ii -p llvm-hs +RTS -p -xc

opt:  $(SRC)
	stack -j9 build --system-ghc --ghc-options="-O2" &&\
	ln -sf $(EXE) ./$(NAME)

$(NAME): $(SRC)
	stack -j9 build --system-ghc --fast --ghc-options="-dynamic" &&\
	ln -sf $(EXE) ./$(NAME)
#|| echo "If you don't have nixos, set enable: false in the stack.yaml:15 (and make sure you have llvm installed)"
	@touch $(NAME) # since stack does nothing if you modify a file without changing code
