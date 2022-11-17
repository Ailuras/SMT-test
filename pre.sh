# 首先处理QF_LIA

input_directory="/home/hanrui/OMT_LIA"
output_directory="/home/hanrui/SMT-test/results"
path_directory="/home/hanrui/SMT-test/OMT_LIA_path"
num_groups=200

mkdir -p "$path_directory"
rm -rf "$path_directory"/*

# 获取文件夹下所有文件的路径，并将它们分为num_groups组
find "$input_directory" -type f > all_files.txt
split -l $((($(wc -l < all_files.txt) + num_groups - 1) / num_groups)) all_files.txt "${path_directory}/group_"
# 删除临时文件
rm all_files.txt
rm nohup.out
# 遍历所有组文件，并使用gen_omt脚本处理每一组
for group_file in "${path_directory}/group_"*; do
    nohup python scripts/gen_omt.py $group_file &
done