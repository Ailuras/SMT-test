#!/bin/bash

input_file="$1"
output_dir="$2"
input_dir="$3"
res_dir="$4"

while read -r file_path; do
    # 在这里处理每个文件，例如：
    relative_path=${file_path#$input_dir}
    new_file_path="${output_dir}${relative_path}"
    res_file_path="${res_dir}${relative_path}"
    new_file_dir=$(dirname "$new_file_path")

    mkdir -p "$new_file_dir"

    # 在这里执行你需要的文件处理操作
    # 检查$res_file_path文件的第一行是否是'sat'
    if [[ $(head -n 1 $res_file_path) == "sat" ]]; then

        # 1. 将$file_path中前三行追加到新文件$new_file_path中
        head -n 3 $file_path > $new_file_path

        # 获取$res_file_path文件的总行数
        total_lines=$(wc -l < $res_file_path)

        # 计算我们需要提取的行范围
        start_line=3
        end_line=$((total_lines - 2))

        # 2. 提取$res_file_path文件中的行并追加到$new_file_path文件中
        sed -n "${start_line},${end_line}p" $res_file_path >> $new_file_path

        # 3. 将$file_path中从第三行开始的不以“((declare-fun”开头的行追加到新文件$new_file_path中
        tail -n +4 $file_path | grep -v "^(declare-fun" >> $new_file_path
    fi

done < "$input_file"