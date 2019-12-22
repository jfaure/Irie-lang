# stack does nothing (except take 1 sec to realize) if no work is necessary

NAME	=	arya
SrcDir	= 	compiler/

EXE	=	$$(stack path --local-install-root)/bin/$(NAME)-exe
SRC	:=	$(shell find $(SrcDir) -type f -name '*.hs')

all: $(NAME)

$(NAME): $(SRC)
	stack -j4 build --fast &&\
	ln -sf $(EXE) ./$(NAME)
	@touch $(NAME) # since stack does nothing if you modify a file without changing code
