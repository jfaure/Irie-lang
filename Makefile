NAME	=	plop

all: $(NAME)

$(NAME): src/CoreSyn.hs src/ToCore.hs src/Main.hs src/ParseSyntax.hs src/Parser.hs src/CmdLine.hs
	stack -j4 build &&\
	ln -sf $$(stack path --local-install-root)/bin/$(NAME)-exe ./$(NAME)
