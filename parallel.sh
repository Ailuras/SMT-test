#!/bin/bash
# ./parallel.sh 40 optimathsat 1200 OMT_LIA
# ./parallel.sh 40 z3pp_ls 1200 OMT_LIA

# 定义输入目录和输出目录
input_directory="/home/hanrui/QF_SLIA"
output_directory="/home/hanrui/SMT-test/results"
path_directory="/home/hanrui/SMT-test/QF_SLIA_unknown"


# ./parallel.sh 40 s3n 1200 QF_SLIA

# 输入参数
num_groups="$1"
solver="$2"
time_t="$3"
res_dir="$4"

# # 创建输出目录
# mkdir -p "$output_directory"
# mkdir -p "$path_directory"
# rm -rf "$path_directory"/*

# # 获取文件夹下所有文件的路径，并将它们分为num_groups组
# find "$input_directory" -type f > all_files.txt
# split -l $((($(wc -l < all_files.txt) + num_groups - 1) / num_groups)) all_files.txt "${path_directory}/group_"
# # 删除临时文件
# rm all_files.txt

mkdir -p "$output_directory/$solver/$res_dir"
rm -rf "$output_directory/$solver/$res_dir"/*
# 遍历所有组文件，并使用run.sh脚本处理每一组
for group_file in "${path_directory}/group_"*; do
    group_name=$(basename "$group_file")
    nohup ./run.sh "$group_file" "$input_directory" "$solver" "$time_t" > "${output_directory}/${solver}/${res_dir}/${group_name}.log" 2>&1 &
done
