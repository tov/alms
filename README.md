# Alms – An Affine Language with Modules and Subtyping

This is a prototype implementation of Alms, an affine language with
modules and subtyping.

Please see http://users.eecs.northwestern.edu/~jesse/pubs/alms/ for more
information.

## Contents

  * [Getting Started](#getting-started)
  * [What to Try](#what-to-try)
  * [Paper Syntax Versus ASCII Syntax](#paper-syntax-versus-ascii-syntax)
  * [Building Alms](#building-alms)
      * [Editline Trouble](#editline-trouble)

## Getting Started

Alms is no longer maintained, and does not build with the latest GHC.
In particular, it is known to work with GHC 7.6.3, and and likely no
longer works with GHC 6. It also does not work with GHC 8.

Thus, the recommended way to try out Alms is via a Docker image,
[jessetov/alms](https://hub.docker.com/r/jessetov/alms/). If you have
Docker installed, you can get a shell with:

    % docker run -it --rm jessetov/alms

That will give you a root shell in the `/alms` directory, which will
contain an `alms` interpreter executable, which you can run:

    # ./alms
    Alms, version 0.6.9
    #- fun (a, b) -> (a, a)
    it : ∀ 'a `b. 'a * `b → 'a * 'a = #<fn (λ (a, b) → (a, a))>
    #-

Note that one of the tests run by `make test` will fail. This is
expected because the test is intended to be run as a non-root user,
but the Docker image logs in as root.

## What to Try

Examples from the paper and several more are in the examples/
directory.  The examples from section 2 of the POPL submission are in:

  * `examples/ex60-popl-deposit.alms`
  * `examples/ex61-popl-AfArray.alms`
  * `examples/ex62-popl-AfArray-type-error.alms`
  * `examples/ex63-popl-CapArray.alms`
  * `examples/ex64-popl-CapLockArray.alms`
  * `examples/ex65-popl-Fractional.alms`
  * `examples/ex66-popl-RWLock.alms`

Other notable examples include two implementations of session types,
an implementation of Sutherland-Hodgman re-entrant polygon clipping
(1974) using session types, and the tracked Berkeley Sockets API from
our ESOP 2010 paper:

  * `lib/libsessiontype.alms`
  * `lib/libsessiontype2.alms`
  * `examples/session-types-polygons.alms`
  * `lib/libsocketcap.alms`

The echo server from the ESOP paper, which uses libsocketcap, is in
examples/echoServer.alms.  To try it, listening on port 10000, run:

    % ./alms examples/echoServer.alms 10000

To connect to the echo server, you can run

    % ./alms examples/netcat.alms localhost 10000

from another terminal.

The examples directory contains many more examples, many of which are
small, but demonstrate type or contract errors -- the comment at the
top of each example says what to expect.  Run many of the examples
with:

    % make examples

Or run the examples as regression tests (quietly):

    % make tests

Of course, you can also run the interpreter in interactive mode:

    % ./alms

You can load libraries from the command line like this:

    % ./alms -lsocketcap

Or from within the REPL like this:

    #- #load "libsocketcap"

Finally, it may be helpful to know about the #i command for asking the
REPL about identifiers:

    #- #i list Exn *
    type +`a list : `a = (::) of `a * `a list | ([])   -- built-in
    module Exn    -- defined at lib/libbasis.alms:198:1-32
    type +`a * +`b : `a \/ `b   -- built-in
    val ( * ) : int -> int -> int   -- built-in


## Paper Syntax Versus ASCII SYntax

The language as presented in the paper is faithful to the language as
implemented, except for issues of pretty printing:

LaTeX (what the paper says)  | ASCII (what you type)      | (what for)
---------------------------- | -------------------------- | -----------
`\forall` `\exists` `\lambda` | `all` `ex` `fun` | (binders)
`\alpha`                     | `’a`          | (unlimited type variable)
`\hat\alpha`                 | `‘a`          | (affine type variable)
`\to^A`                      | `-A>`         | (affine arrow)
`\to^{\hat\alpha}`           | `-a>`         | (arrow with qualifier)
`\sqcup`                     | `\/`          | (qualifier join)
`\pm \baro + -`              | `=` `0` `+` `-` | (variances)


## Building Alms

Provided that a not-too-recent ghc is in your path, to build on UNIX
it ought to be be sufficient to type:

    % make

This should produce an executable `alms` in the current directory,

If this fails, it may also be necessary to either install the editline
package first or disable line editing (Please see EDITLINE TROUBLE).

On Windows, build with Cabal:

    > runghc Setup.hs configure
    > runghc Setup.hs build

This produces an executable in "dist\build\alms\alms".

Cabal should work on UNIX as well, but mixing Cabal and make leads to
linker errors, so it's probably best to stick with one or the other.


### Editline Trouble

Line editing is enabled in the REPL by default, which depends on the
editline Cabal package.  If make fails and says something about
editline, then there are three options:

1)  Use readline instead:

        % make clean; make FLAGS=readline

    or

        % cabal install --flags="readline" alms

2)  Disable line editing:

        % make clean; make FLAGS=-editline

    or

        % cabal install --flags="-editline" alms

3)  Try to install editline or readline . . .

Installing editline can be kind of touchy.  On my system,

    % cabal install editline

seemed to install it, but Cabal still couldn't find it when
building this program.  Installing editline globally made it work:

    % sudo cabal install --global editline

(Likewise, readline didn't work until I installed it globally.)

At this point, older versions of Cabal may give the installed library
bad permissions, so something like this may help, depending on where
it installs things:

    % sudo chmod -R a+rX /usr/local/lib/editline*

If the cabal installation of the GHC package fails, it may be
necessary first to install the C library that it depends on.  The
source is available at http://www.thrysoee.dk/editline/.  On my Debian
system, I was able to install it with:

    % sudo aptitude install libedit2 libedit-dev

Note that libeditline is a *completely different* library, and
installing that will not help.

