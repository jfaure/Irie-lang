NAME	=	irie
SrcDir	= 	compiler/

EXE	=	$$(cabal exec which irie-exe)
SRC	:=	$(shell find $(SrcDir) -type f -name '*.hs')

all: $(NAME)
$(NAME): $(SRC)
fast: $(SRC) requires_nix_shell
	cabal repl
build: all
	cabal build && ln -sf $(EXE) ./$(NAME)

# --ghci-options "-interactive-print=Text.Pretty.Simple.pPrint" --system-ghc --no-build --ghc-options="-j -fbyte-code -dynamic +RTS -A128m -n2m -RTS"
# --ghc-options="-j -fbyte-code -dynamic +RTS -A128m -n2m -RTS -XNoImplicitPrelude"
#

requires_nix_shell:
	@ [ "$(IN_NIX_SHELL)" ] || echo "The $(MAKECMDGOALS) target must be run from inside a nix shell"
	@ [ "$(IN_NIX_SHELL)" ] || (echo "    run 'nix develop' first" && false)

haddock: requires_nix_shell
	cabal haddock --haddock-executables --haddock-html --haddock-hoogle --builddir=haddock

hoogleUnified: requires_nix_shell
	-pkill hoogle
	hoogle generate --local="$$(dirname $$(dirname $$(readlink $$(which hoogle))))"/share/doc/hoogle/ --local=haddock --database=hoo/loc.hoo
	hoogle server --local --database=hoo/loc.hoo -p 8082 >> /dev/null &

hoogle: requires_nix_shell
	-pkill hoogle
	cp "/nix/store/pclnj2dnx8h2xszcsi3mapdr52c7yrnl-hoogle-with-packages/share/doc/hoogle/default.hoo" hoo/local.hoo
	hoogle generate --local=haddock --database=hoo/local.hoo
	hoogle server --local -p 8080 >> /dev/null &
	hoogle server --local --database=hoo/local.hoo -p 8081 >> /dev/null &
