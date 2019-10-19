NAME	=	plop
EXE	=	$$(stack path --local-install-root)/bin/$(NAME)-exe

all: $(NAME)
SrcDir: compiler/
SRCS: $(CoreSyn.hs ToCore.hs Main.hs ParseSyntax.hs Parser.hs CmdLine.hs TypeJudge.hs)


$(NAME): $(shell find $(SrcDir) -type f -name *.hs)
	stack -j4 build --fast &&\
	ln -sf $(EXE) ./$(NAME)
