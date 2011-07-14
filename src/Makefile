## The Cabalized Makefile in the parent directory is the
## preferred way to build, but sometimes this is convenient.

GHC      = ghc
GHCI     = ghci
EXE      = alms
EXAMPLES = ../examples
SRC      = $(HS_SRC) $(HSBOOT_SRC)
HS_SRC   = *.hs \
           Alt/*.hs \
           AST/*.hs \
           Basis/*.hs \
           Basis/Channel/*.hs \
           Data/*.hs \
           Message/*.hs \
           Meta/*.hs \
           Statics/*.hs \
           Syntax/*.hs \
           Type/*.hs \
           Util/*.hs
HSBOOT_SRC  = AST/*.hs-boot

HCOPTS  = -W -Wall -O0 $(EDITING) $(PARSEC) $(NOWARN) $(IMPARR) $(UNICODE)
HIOPTS  = $(NOWARN) $(IMPARR) $(UNICODE)
EDITING = -DUSE_READLINE=System.Console.Editline.Readline
PARSEC  = -DPARSEC_VERSION=3
# IMPARR  = -DANNOTATION_PRINTING_RULE=Rule0
NOWARN  = -fno-warn-unused-do-bind -fno-warn-orphans
UNICODE = -DUNICODE

$(EXE) $(EXE)-%: $(SRC)
	$(GHC) -o $@ --make Main.hs $(HCOPTS)

%.hi: $(HS_SRC) $(HSBOOT_SRC)
	$(GHC) --make $*.hs $(HCOPTS)

%.i:
	$(GHCI) \*$* $(HIOPTS) -XQuasiQuotes

$(EXE)-%:     GHC     = ghc-$*
$(EXE)-6.8.%: EDITING = -DUSE_READLINE=System.Console.Readline
$(EXE)-6.%:   PARSEC  = -DPARSEC_VERSION=2

not-compiled:
	@find . -name \*.hs | sed 's@^\./@@' | while read hs; do \
		hi=`echo $$hs | sed 's/hs$$/hi/'`; \
		test -f $$hi || echo $$hs; \
	done

clean:
	$(RM) $(HS_SRC:.hs=.hi) $(HS_SRC:.hs=.o)
	$(RM) $(HSBOOT_SRC:.hs-boot=.hi-boot) $(HSBOOT_SRC:.hs-boot=.o-boot)
	$(RM) $(EXE) $(EXE)-6.*

wc.%:
	find .. -name \*."$*" | xargs wc -l

test tests: $(EXE)
	@$(EXAMPLES)/run-tests.sh ./$(EXE) $(EXAMPLES)

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
