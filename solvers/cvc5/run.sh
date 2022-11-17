#！/bin/bash
cvc5=solvers/cvc5/bin/cvc5
bench=$1
ulimit -t $2

function trywith {
  limit=$1; shift;
  result="$({ ulimit -S -t "$limit"; $cvc5 -L smt2.6 --no-incremental --no-type-checking --no-interactive "$@" $bench; } 2>&1)"
  case "$result" in
    sat|unsat) echo "$result"; exit 0;;
    *)         echo "unknown";;
  esac
}
function finishwith {
  result="$({ $cvc5 -L smt2.6 --no-incremental --no-type-checking --no-interactive "$@" $bench; } 2>&1)"
  echo "$result"
}

# QF_NRA)
# trywith 600 --decision=justification
# trywith 300 --decision=internal --no-nl-cad --nl-ext=full --nl-ext-tplanes
# finishwith --decision=internal --nl-ext=none

# QF_S|QF_SLIA)
trywith 300 --strings-exp --strings-fmf --no-jh-rlv-order
finishwith --strings-exp --no-jh-rlv-order