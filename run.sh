#!/bin/bash

input_file="$1"
input_dir="$2"
solver="$3"
time_t="$4"

while read -r file_path; do
    # 在这里处理每个文件，例如：
    folder=$(basename $input_dir)
    relative_path=${file_path#$input_dir}
    new_file_path="${folder}${relative_path}"

    # 在这里执行你需要的文件处理操作
    echo --------------------------------------------------
    start=$[$(date +%s%N)/1000000]
    if [ "$solver"x = "z3"x ]; then
        ./solvers/z3/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "cvc5"x ]; then
        ./solvers/cvc5/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "cvc5_new"x ]; then
        timeout $time_t /home/hanrui/cvc5/build/bin/cvc5 $file_path
    fi
    if [ "$solver"x = "yices2"x ]; then
        ./solvers/yices2/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "mathsat5"x ]; then
        ./solvers/mathsat/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "smtrat"x ]; then
        ./solvers/smtrat/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "z3_UD"x ]; then
        ./solvers/z3_UD/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "ismt"x ]; then
        ./solvers/ismt/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "ismt-yices2"x ]; then
        ./solvers/ismt-yices2/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "optimathsat"x ]; then
        ./solvers/optimathsat/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "z3pp"x ]; then
        ./solvers/z3pp/run.sh $file_path $time_t
    fi
    if [ "$solver"x = "z3pp_ls"x ]; then
        ./solvers/z3pp_ls/run.sh $file_path $time_t
    fi
    end=$[$(date +%s%N)/1000000]
    take=$(( end - start ))
    echo $new_file_path : ${take} ms.
done < "$input_file"
