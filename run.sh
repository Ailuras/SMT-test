#!/bin/bash

input_file="$1"
timeout="$2"

while read -r smt2_file; do
    file_name=$(basename "$smt2_file")
    parent_dir=$(basename "$(dirname "$(dirname "$smt2_file")")")

    echo "--------------------------------------------------"
    
    if [[ ! -f "$smt2_file" ]]; then
        echo "Error: .smt2 file not found: $smt2_file"
        continue
    fi
    
    if [[ "$parent_dir" == "QF_LIA" ]]; then
        solver_command="timeout $timeout ./solvers/yices2/yices_smt2 --incremental $smt2_file"
    elif [[ "$parent_dir" == "QF_LRA" ]]; then
        solver_command="timeout $timeout ./solvers/opensmt/opensmt $smt2_file"
    elif [[ "$parent_dir" == "QF_NIA" ]]; then
        solver_command="timeout $timeout ./solvers/smtinterpol/smtinterpol $smt2_file"
    else
        echo "Unknown theory: $parent_dir"
        continue
    fi
    
    start=$[$(date +%s%N)/1000000]

    # echo "$solver_command"
    $solver_command
    
    end=$[$(date +%s%N)/1000000]
    duration=$(( end - start ))
    
    echo "$smt2_file : ${duration} ms."
    
done < "$input_file"
