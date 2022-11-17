import re
import random
import os
import sys

def has_optimization_target(content):
    return '(minimize' in content or '(maximize' in content

def has_optimization_output(content):
    return '(get-objectives)' in content

def modify_file(file_path):
    # 读取文件内容
    if file_path[-5:] != ".smt2":
        print(f"{file_path}: 文件名不符合要求, 删除文件")
        os.remove(file_path)
        return
    with open(file_path, 'r') as file:
        content = file.read()

    if "(set-info :status sat)" not in content or "(check-sat)" not in content:
        print("不是SAT的smt公式, 删除文件")
        os.remove(file_path)
        return
    
    # 统计以 "(de" 为前缀的行的个数
    de_lines_count = len(re.findall(r'\(de', content))

    if de_lines_count < 1000:
        print(f"变量少于1000, 删除文件")
        os.remove(file_path)
        return

    if has_optimization_target(content) and has_optimization_output(content):
        print(f"{file_path}: 文件中已存在优化目标，不做修改")
        return

    # 正则表达式匹配声明语句
    declare_pattern = re.compile(r'declare-fun (\S+) \(\) Int')
    matches = declare_pattern.findall(content)
    if not matches:
        declare_pattern = re.compile(r'\(declare-const (\w+) Int\)')
        matches = declare_pattern.findall(content)
        if not matches:
            print(f"{file_path}: 未找到声明语句，删除文件")
            os.remove(file_path)
            return

    # 随机选择一个变量
    target_variable = random.choice(matches)

    # 随机生成优化目标
    optimization_target = random.choice(['(minimize {})'.format(target_variable),
                                         '(maximize {})'.format(target_variable)])

    # 在文件中插入优化目标
    if not has_optimization_target(content):
        check_sat_pattern = re.compile(r'\(check-sat\)')
        content = check_sat_pattern.sub('{}\n{}'.format(optimization_target, r'\g<0>'), content, count=1)
        
    if not has_optimization_output(content):
        content = content.replace("(check-sat)", "(check-sat)\n(get-objectives)")

    # 写入修改后的内容到文件
    with open(file_path, 'w') as file:
        file.write(content)

    print(f"{file_path}: 文件修改成功")

# modify_file("test.smt2")

group = sys.argv[1]
with open(group) as f:
    file_list = f.readlines()
    for line in file_list:
        file_path = line.strip()
        modify_file(file_path)