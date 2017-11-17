#! /usr/bin/env bash

cd examples

out=`mktemp`
for mode in fast slow; do
  echo "Mode: $mode"

  for example in *.b; do
    echo $example

    fname="${example%.*}"
    infile="$fname.in"
    outfile="$fname.out"

    if [[ -e $infile ]]; then
      quickie $example "--$mode" < $infile > $out
    else
      quickie $example "--$mode" > $out
    fi

    diff $outfile $out || echo ""
  done

  echo
done
rm $out
