EXE      = alms
GHC      = ghc
EXAMPLES = examples

DOC      = dist/doc/html/alms/alms/

default: Setup dist/setup-config
	./Setup build
	cp dist/build/alms/alms .

dist/setup-config config: Setup alms.cabal
	./Setup configure --flags="$(FLAGS)"

Setup: Setup.hs
	$(GHC) -o $@ --make $<

$(EXE): default

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

$(DOC): Setup $(wildcard src/*.hs)
	./Setup haddock --executables

doc: $(DOC)
	$(RM) html
	ln -s $(DOC) html

clean:
	$(RM) *.hi *.o $(EXE) $(TARBALL) Setup
	$(RM) -Rf $(DISTDIR) dist
	$(RM) html


VERSION = 0.12.0
DISTDIR = alms-$(VERSION)
TARBALL = $(DISTDIR).tar.gz

dist: $(TARBALL)

$(TARBALL):
	$(RM) -Rf $(TARBALL) $(DISTDIR)
	svn export . $(DISTDIR)
	tar czf $(TARBALL) $(DISTDIR)
	$(RM) -Rf $(DISTDIR)
	chmod a+r $(TARBALL)
