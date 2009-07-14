EXE     = affine
GHC     = ghc

default: Setup dist/setup-config
	./Setup build
	cp dist/build/affine/affine .

dist/setup-config config: Setup affine.cabal
	./Setup configure

Setup: Setup.hs
	$(GHC) -o $@ --make $<

$(EXE): default


examples: $(EXE)
	for i in examples/ex*.aff; do \
	  echo "$$i"; \
	  head -1 $$i; \
	  ./$(EXE) $$i; \
	  echo; \
	done
	for i in examples/*.in; do \
	  out="`echo $$i | sed 's/\.in$$/.out/'`"; \
	  aff="`echo $$i | sed 's/-[[:digit:]]*\.in$$/.aff/'`"; \
	  echo "$$i (should produce no output)"; \
	  ./$(EXE) "$$aff" < "$$i" | diff "$$out" - ; \
	  echo; \
	done

clean:
	$(RM) *.hi *.o $(EXE) $(TARBALL) Setup
	$(RM) -Rf $(DISTDIR) dist


VERSION = 0.7.0
DISTDIR = affine-contracts-$(VERSION)
TARBALL = $(DISTDIR).tar.gz

dist: $(TARBALL)

$(TARBALL):
	$(RM) -Rf $(TARBALL) $(DISTDIR)
	svn export . $(DISTDIR)
	tar czf $(TARBALL) $(DISTDIR)
	$(RM) -Rf $(DISTDIR)
	chmod a+r $(TARBALL)
