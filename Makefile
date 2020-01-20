# stack is very slow to realize that sometimes no work is necessary

NAME	=	arya
SrcDir	= 	compiler/

EXE	=	$$(stack path --local-install-root)/bin/$(NAME)-exe
SRC	:=	$(shell find $(SrcDir) -type f -name '*.hs')

all: $(NAME)

$(NAME): $(SRC)
	stack -j9 build --fast &&\
	ln -sf $(EXE) ./$(NAME)
	@touch $(NAME) # since stack does nothing if you modify a file without changing code
