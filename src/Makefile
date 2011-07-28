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
HSBOOT_SRC  = AST/*.hs-boot Statics/*.hs-boot

HCOPTS  = -W -Wall -O0 $(EDITING) $(PARSEC) $(HIOPTS)
HIOPTS  = $(NOWARN) $(UNICODE) $(LANGUAGE)
EDITING = -DUSE_READLINE=System.Console.Editline.Readline
PARSEC  = -DPARSEC_VERSION=3
NOWARN  = -fno-warn-unused-do-bind -fno-warn-orphans
UNICODE = -DUNICODE
LANGUAGE= `sed 's/^/-X/' extensions.txt`

PROFILING = -prof -auto-all -osuf p_o -rtsopts

$(EXE) $(EXE)-%: $(SRC)
	$(GHC) -o $@ --make Main.hs $(HCOPTS)

$(EXE)_p: $(EXE)
	$(GHC) -o $@ --make Main.hs $(HCOPTS) $(PROFILING)

%.hi: $(HS_SRC) $(HSBOOT_SRC)
	$(GHC) --make `echo "$*" | sed 's@\.@/@g'`.hs $(HCOPTS)

%.i:
	$(GHCI) \*`echo "$*" | sed 's@\.@/@g'` $(HIOPTS)

$(EXE)-%:     GHC     = ghc-$*
$(EXE)-6.%:   PARSEC  = -DPARSEC_VERSION=2
$(EXE)-6.%:   HCOPTS += -F -pgmF ../ghc6-quasis.sh

not-compiled:
	@find . -name \*.hs | sed 's@^\./@@' | while read hs; do \
		hi=`echo $$hs | sed 's/hs$$/hi/'`; \
		test -f $$hi || echo $$hs; \
	done

clean:
	$(RM) $(HS_SRC:.hs=.hi) $(HS_SRC:.hs=.o)
	$(RM) $(HSBOOT_SRC:.hs-boot=.hi-boot) $(HSBOOT_SRC:.hs-boot=.o-boot)
	$(RM) $(HS_SRC:.hs=.p_o) $(HSBOOT_SRC:.hs-boot=.p_o-boot) *.prof
	$(RM) $(EXE) $(EXE)-6.*

wc.%:
	find .. -name \*."$*" | xargs wc -l | sed 's/$$/ lines/'
	@find .. -name \*."$*" | wc -l | sed 's/$$/ total .$* files/'

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
