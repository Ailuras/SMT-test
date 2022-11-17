#!/bin/bash

# 指定要处理的文件夹路径
target_directory="/home/hanrui/bench-symba"
# target_directory="OMT_LIA_path"

# 要插入的文字
start_line="(set-logic QF_LIA)"
end_line=""

# 遍历目录下的所有文件
for file in "$target_directory"/*; do
    if [ -f "$file" ]; then
        # 在文件开始插入一行文字
        echo "$start_line" | cat - "$file" > temp && mv temp "$file"
        # 在文件结尾插入一行文字
        echo "" >> "$file"
        echo "$end_line" >> "$file"
    fi
done

echo "已完成对文件夹内所有文件的处理。"
