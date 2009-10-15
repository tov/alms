#!/bin/sh

exe="$1"
test="$2"

case "$test" in
  */ex*|ex*)
    echo "$test";
    if ! ./"$exe" "$test" > /dev/null; then
      echo
      echo "TEST FAILED:"
      head -1 "$test"
      echo
    fi >&2
  ;;
  *)
    (
      echo "TEST FAILED:"
      echo "Couldn't figure out how to run $test"
    ) >&2
  ;;
esac
