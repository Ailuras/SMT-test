import os
import re
import pandas as pd
from concurrent.futures import ThreadPoolExecutor

def process_constraint_utilization(file_path, total_constraints):
    with open(file_path, 'r') as f:
        content = f.read().strip()

    lines = content.splitlines()
    content_stack = [0]
    constraint_count_per_subexample = []
    
    for line in lines:
        if "(push 1)" in line:
            content_stack.append(0)
        elif "(pop 1)" in line:
            if len(content_stack) > 1:
                content_stack.pop()
        elif "(check-sat)" in line:
            constraint_count_per_subexample.append(sum(content_stack))
        elif "(assert" in line:
            content_stack[-1] += 1
    
    avg_constraints = sum(constraint_count_per_subexample) / len(constraint_count_per_subexample) if constraint_count_per_subexample else 0
    return avg_constraints / total_constraints if total_constraints > 0 else 0

def process_smt2_file(file_path):
    with open(file_path, 'r') as f:
        content = f.read()
    
    source_dir = os.path.basename(os.path.dirname(file_path))
    parent_dir = os.path.basename(os.path.dirname(os.path.dirname(file_path)))
    
    check_sat_count = len(re.findall(r"\(check-sat\)", content))
    declare_const_count = len(re.findall(r"\(declare-const", content)) + len(re.findall(r"\(declare-fun", content))
    
    assert_count = len(re.findall(r"\(assert", content))
    
    file_name = os.path.basename(file_path)
    
    del content
    
    avg_constraint_utilization = process_constraint_utilization(file_path, assert_count)
    
    return {
        "File": file_name,
        "Theory": parent_dir,
        "Source": source_dir,
        "Subexamples": check_sat_count,
        "Variables": declare_const_count,
        "Total Constraints": assert_count,
        "Avg Constraint Utilization": avg_constraint_utilization,
        "#Solved Subexamples": 0,
        "Solve Time (s)": 0,
        "#Solved Sat": 0,
        "Result": "Not Solved",
        "Individual Solve Time (s)": 0,
        "Speedup": 0
    }

def process_log_file(log_file_path):
    log_info = []

    with open(log_file_path, 'r') as log_file:
        content = log_file.read().strip()
        
        segments = content.split('--------------------------------------------------')

        for segment in segments:
            sat_count = len(re.findall(r"\bsat\b", segment))
            unsat_count = len(re.findall(r"\bunsat\b", segment))

            match = re.search(r"(incremental/.+\.smt2) : (\d+) ms\.$", segment.strip().split('\n')[-1])
            if match:
                smt_file_path = match.group(1)
                solve_time_ms = int(match.group(2))
                
                smt_file_name = os.path.basename(smt_file_path)
                path_parts = smt_file_path.split('/')
                theory = path_parts[1]
                source = path_parts[2]
                
                log_info.append({
                    "SmtFileName": smt_file_name,
                    "Theory": theory,
                    "Source": source,
                    "Sat Count": sat_count,
                    "Unsat Count": unsat_count,
                    "Solve Time (ms)": solve_time_ms
                })
    
    return log_info

def process_log_file_solved(log_file_path):
    solved_times = {}

    with open(log_file_path, 'r') as log_file:
        content = log_file.read().strip()
        
        segments = content.split('--------------------------------------------------')

        for segment in segments:
            match = re.search(r"(benchmarks/.+/([^/]+))_\d+\.smt2 : (\d+) ms\.$", segment.strip().split('\n')[-1])
            if match:
                problem_name = match.group(2)
                solve_time_ms = int(match.group(3))

                if problem_name not in solved_times:
                    solved_times[problem_name] = 0
                solved_times[problem_name] += solve_time_ms
    
    return solved_times

def gather_data(base_dir, results_dir, results_dir_solved):
    result = []
    
    with ThreadPoolExecutor(max_workers=4) as executor:
        smt2_files = [os.path.join(root, file) for root, dirs, files in os.walk(base_dir) for file in files if file.endswith(".smt2")]
        smt2_data = list(executor.map(process_smt2_file, smt2_files))
    
    log_info = []
    solved_times = {}

    for log_file in os.listdir(results_dir):
        if log_file.endswith(".log"):
            log_file_path = os.path.join(results_dir, log_file)
            log_info.extend(process_log_file(log_file_path))
            
    for log_file in os.listdir(results_dir_solved):
        if log_file.endswith(".log"):
            log_file_path = os.path.join(results_dir_solved, log_file)
            solved_data = process_log_file_solved(log_file_path)
            for problem, time in solved_data.items():
                if problem in solved_times:
                    solved_times[problem] += time
                else:
                    solved_times[problem] = time
    
    for data in smt2_data:
        for log_entry in log_info:
            if log_entry["SmtFileName"] == data["File"] and log_entry["Theory"] == data["Theory"] and log_entry["Source"] == data["Source"]:
                data["#Solved Subexamples"] = log_entry["Sat Count"] + log_entry["Unsat Count"]
                data["Solve Time (s)"] = log_entry["Solve Time (ms)"] / 1000
                data["#Solved Sat"] = log_entry["Sat Count"]
                
                if data["#Solved Subexamples"] < data["Subexamples"]:
                    data["Result"] = "Not Solved"
                else:
                    data["Result"] = "Solved"
                break
        
        problem_name = data["File"]
        if problem_name in solved_times:
            data["Individual Solve Time (s)"] = solved_times[problem_name] / 1000  # Convert to seconds
            if data["Solve Time (s)"] > 0:
                data["Speedup"] = data["Individual Solve Time (s)"] / data["Solve Time (s)"]
            else:
                data["Speedup"] = 0
        
        result.append(data)
    
    return result

def save_to_excel(data, output_file):
    df = pd.DataFrame(data)
    df.to_excel(output_file, index=False)

def save_solved_files(data, solved_file_path):
    with open(solved_file_path, 'w') as f:
        for entry in data:
            if entry["Result"] == "Solved" and entry["Subexamples"] <= 1000:
                file_path = os.path.join(base_dir, entry["Theory"], entry["Source"], entry["File"])
                f.write(file_path + '\n')

def main():
    global base_dir
    base_dir = "/home/ailura/SMT-test/incremental"
    results_dir = "/home/ailura/SMT-test/results/all"
    results_dir_solved = "/home/ailura/SMT-test/results/solved"
    output_file = "res.xlsx"
    solved_file_path = "solved_file.log"
    
    data = gather_data(base_dir, results_dir, results_dir_solved)
    save_to_excel(data, output_file)
    save_solved_files(data, solved_file_path)

if __name__ == "__main__":
    main()