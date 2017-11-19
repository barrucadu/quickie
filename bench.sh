#! /usr/bin/env bash

export LC_ALL=en_GB.UTF-8
export LANG=en_GB.UTF-8
export LC_CTYPE=en_GB.UTF-8

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
cat > "$d/shim.c" <<EOF
char mem[40000] = {0};

void bfmain(char**, int);

int main(void) {
  bfmain((char**)&mem, 10000);
  return 0;
}
EOF
for example in *.b; do
  fname="${example%.*}"
  infile="$fname.in"

  quickie $example -o "$d/$example.o"
  gcc "$d/shim.c" "$d/$example.o" -o "$d/$example"

  if [[ -e $infile ]]; then
    bench "$d/$example < $infile"
  else
    bench "$d/$example"
  fi
done
rm -r $d
