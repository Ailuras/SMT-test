#!/bin/bash

input_file="$1"
output_dir="$2"
input_dir="$3"
path="$4"

while read -r file_path; do
    # 在这里处理每个文件，例如：
    relative_path=${file_path#$input_dir}
    new_file_path="${output_dir}${relative_path}"

    # 在这里执行你需要的文件处理操作
    var=$(grep -o 'declare-fun' "$file_path" | wc -l)
    model=$(grep -o 'define-fun' "$new_file_path" | wc -l)
    if [ "$var" -eq "$model" ]; then
        echo "$file_path: $var vs $model" >> $path/isEqual.txt
    else
        echo "$file_path: $var vs $model" >> $path/isNotEqual.txt
    fi

done < "$input_file"
