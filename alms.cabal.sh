#!/bin/sh

cat <<EOF
Name:           alms
Version:        `./util`
Copyright:      2012-2018, Jesse A. Tov
Cabal-Version:  >= 1.8
License:        BSD3
License-File:   LICENSE
Stability:      experimental
Author:         Jesse A. Tov <jesse@eecs.northwestern.edu>
Maintainer:     jesse@eecs.northwestern.edu
Homepage:       http://users.eecs.northwestern.edu/~jesse/pubs/alms/
Category:       Compilers/Interpreters
Synopsis:       a practical affine language
Build-type:     Simple
Extra-Source-Files:
                alms.cabal.sh src/extensions.txt
Data-Files:     lib/*.alms examples/*.alms examples/*.sh
                examples/*.in examples/*.out
                README Makefile

Description:
    Alms is an experimental, general-purpose programming language that
    supports practical affine types. To offer the expressiveness of
    Girard’s linear logic while keeping the type system light and
    convenient, Alms uses expressive kinds that minimize notation while
    maximizing polymorphism between affine and unlimited types.

    A key feature of Alms is the ability to introduce abstract affine types
    via ML-style signature ascription. In Alms, an interface can impose
    stiffer resource usage restrictions than the principal usage
    restrictions of its implementation. This form of sealing allows the type
    system to naturally and directly express a variety of resource
    management protocols from special-purpose type systems.

Source-Repository head
  Type:     git
  Location: git://github.com/tov/alms.git

Flag unicode
  Description: Use Unicode symbols for pretty-printing

Flag editline
  Description: Enable line editing using the editline package

Flag parsec3
  Description: Use version 3 of the parsec package

Flag readline
  Description: Enable line editing using the readline package
  Default:     False

Executable alms
  Main-Is:              Main.hs
  Hs-Source-Dirs:       src
  GHC-Options:          -O3
  CPP-Options:          -DALMS_CABAL_BUILD
  Build-Depends:
                        base == 4.*,
                        HUnit >= 1.2,
                        QuickCheck >= 2,
                        array >= 0.3,
                        containers >= 0.1,
                        directory >= 1.0,
                        fgl >= 5,
                        filepath >= 1.1,
                        incremental-sat-solver >= 0.1.7,
                        mtl >= 1.1,
                        network >= 2.2,
                        pretty >= 1,
                        random >= 1,
                        stm >= 2.0,
                        syb >= 0.1,
                        template-haskell >= 2.0,
                        transformers >= 0.2,
                        tuple >= 0.2
  Other-Modules:
EOF

find src -name \*.hs |
    sed 's@^src/@                        @;s@\.hs$@@;s@/@.@g;/^Main$/d'

echo "  Extensions:"

sed 's/^/                        /' src/extensions.txt

cat <<EOF

  if flag(unicode)
    CPP-Options:    -DUNICODE

  if flag(readline)
    Build-Depends:  readline >= 1.0
    CPP-Options:    -DUSE_READLINE=System.Console.Readline
  else
    if flag(editline)
      Build-Depends:  editline >= 0.2.1
      CPP-Options:    -DUSE_READLINE=System.Console.Editline.Readline

  if flag(parsec3)
    Build-Depends:  parsec == 3.*
    CPP-Options:    -DPARSEC_VERSION=3
  else
    Build-Depends:  parsec == 2.*
    CPP-Options:    -DPARSEC_VERSION=2
EOF
