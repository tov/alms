## The Cabalized Makefile in the parent directory is the
## preferred way to build, but sometimes this is convenient.

GHC      = ghc
EXE      = alms
EXAMPLES = ../examples
SRC      = *.hs Basis/*.hs Meta/*.hs

HCOPTS  = -W -Wall -O0 $(EDITING)
EDITING = -DUSE_READLINE=System.Console.Editline.Readline

$(EXE) $(EXE)-%: $(SRC)
	$(GHC) -o $@ --make Main.hs $(HCOPTS)

Basis.hs: basis.alms
	touch $@

$(EXE)-%:     GHC     = ghc-$*
$(EXE)-6.8.%: EDITING = -DUSE_READLINE=System.Console.Readline

clean:
	$(RM) Basis/*.hi Basis/*.o *.hi *.o $(EXE) $(EXE)-6.*

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
