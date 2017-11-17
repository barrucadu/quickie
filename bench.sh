#! /usr/bin/env nix-shell
#! nix-shell -i bash -p haskellPackages.bench

cd examples

for mode in fast slow; do
  echo "Mode: $mode"

  for example in *.b; do
    fname="${example%.*}"
    infile="$fname.in"

    if [[ -e $infile ]]; then
      bench "quickie $example --$mode < $infile"
    else
      bench "quickie $example --$mode"
    fi
  done

  echo
done

echo "Mode: compiled"

d=`mktemp -d`
for example in *.b; do
  fname="${example%.*}"
  infile="$fname.in"

  quickie $example -o "$d/$example.o"
  gcc "$d/$example.o" -o "$d/$example"

  if [[ -e $infile ]]; then
    bench "$d/$example < $infile"
  else
    bench "$d/$example"
  fi
done
rm -r $d
