#!/bin/bash

input_file="$1"
output_dir="$2"
input_directory="$3"

while read -r file_path; do
    # 在这里处理每个文件，例如：
    relative_path=${file_path#$input_directory}
    new_file_path="${output_dir}${relative_path}"
    new_file_dir=$(dirname "$new_file_path")

    mkdir -p "$new_file_dir"

    # 在这里执行你需要的文件处理操作
    total_lines=$(wc -l < $file_path)
    insert_line=$((total_lines))
    sed "${insert_line}i\\(get-model)" $file_path > $new_file_path


done < "$input_file"
