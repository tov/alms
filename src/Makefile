## The Cabalized Makefile in the parent directory is the
## preferred way to build, but sometimes this is convenient.

GHC     = ghc
EXE     = affine

HCOPTS  = -W -Wall -O0 $(EDITING)
EDITING = -DUSE_READLINE=System.Console.Editline.Readline

$(EXE) $(EXE)-%: *.hs Basis/*.hs
	$(GHC) -o $@ --make Main.hs $(HCOPTS)

$(EXE)-%:     GHC     = ghc-$*
$(EXE)-6.8.%: EDITING = -DUSE_READLINE=System.Console.Readline

clean:
	$(RM) Basis/*.hi Basis/*.o *.hi *.o $(EXE) $(EXE)-6.*

examples: $(EXE)
	@for i in ../examples/ex*.aff; do \
	  echo "$$i"; \
	  head -1 "$$i" | grep . ; \
	  ./$(EXE) "$$i"; \
	  echo; \
	done
	@for i in ../examples/*.in; do \
	  out="`echo $$i | sed 's/\.in$$/.out/'`"; \
	  aff="`echo $$i | sed 's/-[[:digit:]]*\.in$$/.aff/'`"; \
	  echo "$$i"; \
	  ./$(EXE) "$$aff" < "$$i" | diff "$$out" - ; \
	  echo; \
	done

