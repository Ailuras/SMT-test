#!/bin/bash
# ./parallel_simp.sh cvc5_new 1200 QF_SLIA_unknown
# ./parallel_simp.sh cvc5_new 1200 QF_S_unknown

# 定义输入目录和输出目录
input_directory="/home/hanrui/QF_S"
output_directory="/home/hanrui/SMT-test/results"
path_directory="/home/hanrui/SMT-test/QF_S_unknown"

# 输入参数
solver="$1"
time_t="$2"
res_dir="$3"

mkdir -p "$output_directory/$solver/$res_dir"
rm -rf "$output_directory/$solver/$res_dir"/*
# 遍历所有组文件，并使用run.sh脚本处理每一组
for group_file in "${path_directory}/group_"*; do
    group_name=$(basename "$group_file")
    ./run.sh "$group_file" "$input_directory" "$solver" "$time_t" > "${output_directory}/${solver}/${res_dir}/${group_name}.log" 2>&1 &
done
