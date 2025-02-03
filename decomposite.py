import os
import re

def process_smt2_file(file_path):
    with open(file_path, 'r') as f:
        content = f.read().strip()

    lines = content.splitlines()
    content_stack = [[]]
    subexample_count = 1
    output_files = []

    for line in lines:
        if "(push 1)" in line:
            content_stack.append([])
        elif "(pop 1)" in line:
            if len(content_stack) > 1:
                content_stack.pop()
        elif "(check-sat)" in line:
            content_stack[-1].append(line)

            file_name = os.path.basename(file_path)
            clean_name = re.sub(r'[\\/*?:"<>|]', "_", file_name)
            path_parts = file_path.split('/')
            theory = path_parts[-3]  # The theory part (e.g., QF_LIA)

            folder_path = os.path.join("benchmarks", theory, clean_name)
            
            if not os.path.exists(folder_path):
                os.makedirs(folder_path)
            
            subexample_file = os.path.join(folder_path, f"{clean_name}_{subexample_count}.smt2")
            output_files.append(subexample_file)
            
            with open(subexample_file, 'w') as sub_file:
                all_lines = []
                for stack in content_stack:
                    all_lines.extend(stack)

                sub_file.write("\n".join(all_lines))
            
            subexample_count += 1
            content_stack[-1] = content_stack[-1][:-2]
        else:
            content_stack[-1].append(line)

    return output_files

def process_solved_file(solved_file_path):
    with open(solved_file_path, 'r') as f:
        smt2_files = f.readlines()
    
    smt2_files = [line.strip() for line in smt2_files]
    all_subexample_files = []

    for smt2_file in smt2_files:
        smt2_file = smt2_file.strip()
        if os.path.exists(smt2_file):
            output_files = process_smt2_file(smt2_file)
            all_subexample_files.extend(output_files)

    return all_subexample_files

def main():
    solved_file_path = "solved_file.log"
    subexample_files = process_solved_file(solved_file_path)
    
    print("Generated subexamples:")
    for file in subexample_files:
        print(file)

if __name__ == "__main__":
    main()
