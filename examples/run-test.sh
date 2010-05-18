#!/bin/sh

exe="$1"
test="$2"

echo "$test"

case "$test" in
  *-type-error.alms)
    if ! ./"$exe" "$test"  2>&1 |
        grep '^type error: ' > /dev/null; then
      echo
      echo "TEST FAILED (expected type error):"
      head -1 "$test"
      echo
    fi >&2
    ;;
  *-blame-error.alms)
    if ! ./"$exe" "$test"  2>&1 |
        grep ' Blame (' > /dev/null; then
      echo
      echo "TEST FAILED (expected blame error):"
      head -1 "$test"
      echo
    fi >&2
    ;;
  *)
    if ! ./"$exe" "$test" > /dev/null; then
      echo
      echo "TEST FAILED:"
      head -1 "$test"
      echo
    fi >&2
  ;;
esac
