#!/bin/bash

input_file="$1"
output_dir="$2"
input_dir="$3"
path="$4"

while read -r file_path; do
    # 在这里处理每个文件，例如：
    relative_path=${file_path#$input_dir}
    new_file_path="${output_dir}${relative_path}"
    copy_file_path="/home/hanrui/QF_NIA${relative_path}"
    erro_file_path="/pub/data/Ailura/QF_NIA_err"

    if grep -q '(set-info :status sat)' "$file_path"; then
        if [[ $(head -n 1 $new_file_path) == "sat" ]]; then
            echo "$file_path: sat" >> $path/isRight.txt
        elif [[ $(head -n 1 $new_file_path) == "unsat" ]]; then
            cp $copy_file_path $erro_file_path
            echo "$file_path: sat -> unsat" >> $path/isErr.txt
        fi
    fi

    if grep -q '(set-info :status unsat)' "$file_path"; then
        if [[ $(head -n 1 $new_file_path) == "unsat" ]]; then
            echo "$file_path: unsat" >> $path/isRight.txt
        elif [[ $(head -n 1 $new_file_path) == "sat" ]]; then
            cp $copy_file_path $erro_file_path
            echo "$file_path: unsat -> sat" >> $path/isErr.txt
        fi
    fi

done < "$input_file"
