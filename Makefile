EXE      = alms
GHC      = ghc
EXAMPLES = examples
SRC      = $(HS_SRC) $(HSBOOT_SRC)
HS_SRC   = src/*.hs \
           src/Alt/*.hs \
           src/AST/*.hs \
           src/Basis/*.hs \
           src/Basis/Channel/*.hs \
           src/Data/*.hs \
           src/Message/*.hs \
           src/Meta/*.hs \
           src/Statics/*.hs \
           src/Syntax/*.hs \
           src/Type/*.hs \
           src/Util/*.hs
HSBOOT_SRC  = src/AST/*.hs-boot src/Statics/*.hs-boot

DOC      = dist/doc/html/alms/alms/

default: Setup dist/setup-config $(SRC)
	./Setup build
	cp dist/build/alms/alms .

alms.cabal: alms.cabal.sh Makefile src/extensions.txt $(HS_SRC)
	./alms.cabal.sh > alms.cabal

dist/setup-config config: Setup alms.cabal
	./Setup configure --user --flags="$(FLAGS)"

Setup: Setup.hs
	$(GHC) -o $@ --make $<

$(EXE): default

install: $(EXE) Setup
	./Setup install

test tests: $(EXE)
	@$(SHELL) $(EXAMPLES)/run-tests.sh ./$(EXE) $(EXAMPLES)

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

$(DOC): Setup $(wildcard src/*.hs)
	./Setup haddock --executables

doc: $(DOC)
	$(RM) html
	ln -s $(DOC) html

clean:
	$(RM) *.hi *.o $(EXE) $(TARBALL) Setup
	$(RM) -Rf $(DISTDIR) dist
	$(RM) html


VERSION = 0.6.7
DISTDIR = alms-$(VERSION)
TARBALL = $(DISTDIR).tar.gz

dist: $(TARBALL)

$(TARBALL):
	$(RM) -Rf $(TARBALL) $(DISTDIR)
	svn export . $(DISTDIR)
	tar czf $(TARBALL) $(DISTDIR)
	$(RM) -Rf $(DISTDIR)
	chmod a+r $(TARBALL)
