#!/bin/bash
# ./parallel_sat.sh 200
# ./parallel.sh 100 Model-Validation

# 定义输入目录和输出目录
# input_directory="/home/hanrui/QF_NIA_check"
# output_directory="/home/hanrui/QF_NIA_res_1"
# path_directory="QF_NIA_path_res_1"

input_directory="/pub/data/Ailura/QF_NIA_check"
output_directory="/pub/data/Ailura/QF_NIA_res_1"
path_directory="QF_NIA_res"

# input_directory="/home/hanrui/SMT-test/test"
# output_directory="/home/hanrui/SMT-test/test_res"
# path_directory="test_path"

# 输入参数
num_groups="$1"

# 创建输出目录
mkdir -p "$output_directory"
mkdir -p "$path_directory"
rm -rf "$path_directory"/*

# 获取文件夹下所有文件的路径，并将它们分为i组
find "$input_directory" -type f > all_files.txt
split -l $((($(wc -l < all_files.txt) + num_groups - 1) / num_groups)) all_files.txt "${path_directory}/group_"
# 删除临时文件
rm all_files.txt

rm -rf "/pub/data/Ailura/QF_NIA_err"
mkdir -p "/pub/data/Ailura/QF_NIA_err"

mkdir -p "$path_directory/isEqual"
# 遍历所有组文件，并使用run.sh脚本处理每一组
for group_file in "${path_directory}/group_"*; do
    group_name=$(basename "$group_file")
    ./run_sat.sh "$group_file" "$output_directory" "$input_directory" "$path_directory/isEqual" > "${path_directory}/isEqual/${group_name}.txt" 2>&1 &
done
