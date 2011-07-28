#!/bin/sh

# Dirty hack to turn GHC 7 quasiquote syntax (e.g. "[ex|") into
# GHC 6 ("[$ex|").  This relies on the fact that all my quasiquoters
# have alphanumeric names of at least two characters (which
# distinguishes them from built-in TH quasiquotes such as "[d|").

exec sed 's/\[\([a-z][a-zA-Z0-9][a-zA-Z0-9]*\)|/[$\1|/g' "$2" > "$3"
