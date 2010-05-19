## The Cabalized Makefile in the parent directory is the
## preferred way to build, but sometimes this is convenient.

GHC      = ghc
EXE      = alms
EXAMPLES = ../examples
SRC      = $(HS_SRC) $(HSBOOT_SRC)
HS_SRC      = *.hs Basis/*.hs Basis/Channel/*.hs Syntax/*.hs Meta/*.hs
HSBOOT_SRC  = Syntax/*.hs-boot

HCOPTS  = -W -Wall -O0 $(EDITING) $(NOWARN)
EDITING = -DUSE_READLINE=System.Console.Editline.Readline
NOWARN  = -fno-warn-unused-do-bind -fno-warn-orphans

$(EXE) $(EXE)-%: $(SRC)
	$(GHC) -o $@ --make Main.hs $(HCOPTS)

$(EXE)-%:     GHC     = ghc-$*
$(EXE)-6.8.%: EDITING = -DUSE_READLINE=System.Console.Readline

clean:
	$(RM) $(HS_SRC:.hs=.hi) $(HS_SRC:.hs=.o)
	$(RM) $(HSBOOT_SRC:.hs-boot=.hi-boot) $(HSBOOT_SRC:.hs-boot=.o-boot)
	$(RM) $(EXE) $(EXE)-6.*

wc.%:
	find .. -name \*."$*" | xargs wc -l

test tests: $(EXE)
	@for i in $(EXAMPLES)/ex*.alms; do \
	  $(EXAMPLES)/run-test.sh $(EXE) "$$i"; \
	done
	@for i in $(EXAMPLES)/*.in; do \
	  out="`echo $$i | sed 's/\.in$$/.out/'`"; \
	  src="`echo $$i | sed 's/-[[:digit:]]*\.in$$/.alms/'`"; \
	  echo "$$i"; \
	  ./$(EXE) "$$src" < "$$i" | diff "$$out" - ; \
	done

examples: $(EXE)
	@for i in $(EXAMPLES)/ex*.alms; do \
	  echo "$$i"; \
	  head -1 "$$i"; \
	  ./$(EXE) "$$i"; \
	  echo; \
	done
	@for i in $(EXAMPLES)/*.in; do \
	  out="`echo $$i | sed 's/\.in$$/.out/'`"; \
	  src="`echo $$i | sed 's/-[[:digit:]]*\.in$$/.alms/'`"; \
	  echo "$$i"; \
	  ./$(EXE) "$$src" < "$$i"; \
	done
