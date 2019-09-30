NAME	=	plop

all: $(NAME)

$(NAME): src/CoreSyn.hs src/ToCore.hs src/Main.hs src/ParseSyntax.hs src/Parser.hs src/CmdLine.hs src/TypeJudge.hs
	stack -j4 build --fast &&\
	ln -sf $$(stack path --local-install-root)/bin/$(NAME)-exe ./$(NAME)
