#!/bin/bash

# 指定要检查的文件夹路径
folder_path="/home/hanrui/bench-symba"

# 指定要搜索的字符串
search_string="Real"

# 遍历文件夹中的文件
for file in "$folder_path"/*; do
    # 使用grep检查文件中是否包含指定字符串
    if ! grep -q "$search_string" "$file"; then
        # 如果文件中不包含指定字符串，则打印文件名
        echo "$file"
    fi
done

old_string="Real"
new_string="Int"

# 遍历文件夹中的文件
for file in "$folder_path"/*; do
    # 使用sed命令替换文件中的字符串
    sed -i "s/$old_string/$new_string/g" "$file"
done

echo "已完成对文件夹内所有文件的处理。"