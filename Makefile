# stack is very slow to realize that sometimes no work is necessary

NAME	=	nimzo
SrcDir	= 	compiler/

EXE	=	$$(stack path --local-install-root)/bin/$(NAME)-exe
SRC	:=	$(shell find $(SrcDir) -type f -name '*.hs')

all: $(NAME)
fast: $(SRC)
	stack -j9 ghci --no-build --ghc-options="-fbyte-code -dynamic"
# look into: --with-ghc=ghcid 

$(NAME): $(SRC)
	stack -j9 build --fast --ghc-options="-dynamic" &&\
	ln -sf $(EXE) ./$(NAME)
	@touch $(NAME) # since stack does nothing if you modify a file without changing code
