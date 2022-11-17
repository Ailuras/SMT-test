#!/bin/bash

input_file="$1"
output_dir="$2"
input_dir="$3"
path="$4"

while read -r file_path; do
    # 在这里处理每个文件，例如：
    relative_path=${file_path#$input_dir}
    new_file_path="${output_dir}${relative_path}"
    copy_file_path="/pub/data/Ailura/QF_NIA_scr${relative_path}"
    erro_file_path="/pub/data/Ailura/QF_NIA_err"

    # 在这里执行你需要的文件处理操作
    if [[ $(head -n 1 $new_file_path) == "sat" ]]; then
        echo "$file_path: sat" >> $path/isSat.txt
    else
        cp $copy_file_path $erro_file_path
        echo "$file_path: error" >> $path/isErr.txt
    fi

done < "$input_file"
