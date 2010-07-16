#/bin/sh

EXE="$1"
EXAMPLES="$2"
LIB="`dirname "$EXAMPLES"`/lib"

for i in $EXAMPLES/ex*.alms $LIB/lib*.alms; do
  /bin/sh $EXAMPLES/run-test.sh $EXE "$i"
done

for i in $EXAMPLES/*.in; do
  out="`echo $i | sed 's/\.in$/.out/'`"
  src="`echo $i | sed 's/-[[:digit:]]*\.in$/.alms/'`"
  echo "$i"
  $EXE "$src" < "$i" | diff "$out" -
done
