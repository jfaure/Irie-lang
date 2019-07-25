NAME	=	plop

all: $(NAME)

$(NAME): src/Core.hs src/Main.hs src/ParseSyntax.hs src/Parser.hs
	stack -j4 build &&\
	ln -sf $$(stack path --local-install-root)/bin/$(NAME)-exe ./$(NAME)
