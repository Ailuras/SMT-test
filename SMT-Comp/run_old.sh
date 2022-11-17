#！/bin/bash
# ./run.sh test.smt2 1800 mathsat5
time_t=$2
solver=$3

function testAll() {
    if test -f $@;then
        echo --------------------------------------------------
        start=$[$(date +%s%N)/1000000]
        if [ "$solver"x = "z3"x ]; then
            ./solvers/z3/run.sh $@ $time_t
        fi
        if [ "$solver"x = "cvc5"x ]; then
            ./solvers/cvc5/run.sh $@ $time_t
        fi
        if [ "$solver"x = "yices2"x ]; then
            ./solvers/yices2/run.sh $@ $time_t
        fi
        if [ "$solver"x = "mathsat5"x ]; then
            ./solvers/mathsat/run.sh $@ $time_t
        fi
        if [ "$solver"x = "smtrat"x ]; then
            ./solvers/smtrat/run.sh $@ $time_t
        fi
        if [ "$solver"x = "z3_UD"x ]; then
            ./solvers/z3_UD/run.sh $@ $time_t
        fi
        end=$[$(date +%s%N)/1000000]
        take=$(( end - start ))
        echo $@ : ${take} ms.
        return
    fi
    for file in $@/*;do 
        echo --------------------------------------------------
        start=$[$(date +%s%N)/1000000]
        if [ "$solver"x = "z3"x ]; then
            ./solvers/z3/run.sh $file $time_t
        fi
        if [ "$solver"x = "cvc5"x ]; then
            ./solvers/cvc5/run.sh $file $time_t
        fi
        if [ "$solver"x = "yices2"x ]; then
            ./solvers/yices2/run.sh $file $time_t
        fi
        if [ "$solver"x = "mathsat5"x ]; then
            ./solvers/mathsat/run.sh $file $time_t
        fi
        if [ "$solver"x = "smtrat"x ]; then
            ./solvers/smtrat/run.sh $file $time_t
        fi
        if [ "$solver"x = "z3_UD"x ]; then
            ./solvers/z3_UD/run.sh $file $time_t
        fi
        end=$[$(date +%s%N)/1000000]
        take=$(( end - start ))
        echo $file : ${take} ms.
    done
}
# echo 2
testAll $1