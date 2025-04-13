#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Process Solver Results Script
This script processes solver results from log files and updates the Excel report.

Usage:
    python analysis_solve.py --input-excel <excel_file> --log-dir <log_dir1> [<log_dir2> ...] --output-file <output_file>
    
Example:
    python experiments/analysis_solve.py --input-excel charts/Norn.xlsx --log-dir results/cvc5 --output-file charts/Norn_cvc5.xlsx
    python experiments/analysis_solve.py --input-excel charts/Norn.xlsx --log-dir results/cvc5 results/z3 --output-file charts/Norn_cvc5_z3.xlsx
"""

import os
import re
import sys
import pandas as pd
import argparse
from pathlib import Path
from tqdm import tqdm
import openpyxl.styles

def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(description='Process solver results and update Excel report.')
    parser.add_argument('--input-excel', required=True, help='Input Excel file containing benchmark information')
    parser.add_argument('--log-dir', nargs='+', required=True, help='One or more directories containing solver result log files')
    parser.add_argument('--output-file', required=True, help='Output Excel file to save updated results')
    
    return parser.parse_args()

def extract_task_name(log_file):
    """Extract task name from a log file."""
    try:
        with open(log_file, 'r', encoding='utf-8') as f:
            for line in f:
                if line.startswith('TASK:'):
                    return line.split(':', 1)[1].strip()
    except Exception as e:
        print(f"Error reading task name from {log_file}: {e}")
    return None

def parse_log_file(log_file):
    """Parse a log file and extract results for each file."""
    results = {}
    current_file = None
    current_result = {}
    solver_output = []
    collecting_output = False
    
    try:
        with open(log_file, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                
                # Skip empty lines and double separators
                if not line or line.startswith('='):
                    continue
                
                # Parse file information
                if line.startswith('FILE:'):
                    if current_file and current_result:
                        current_result['solver_output'] = '\n'.join(solver_output)
                        results[current_file] = current_result
                    current_file = line.split(':', 1)[1].strip()
                    current_result = {}
                    solver_output = []
                    collecting_output = False
                
                # Parse result information
                elif line.startswith('RESULT:'):
                    current_result['result'] = line.split(':', 1)[1].strip()
                elif line.startswith('SOLVING_TIME:'):
                    current_result['time'] = float(line.split(':', 1)[1].strip())
                elif line.startswith('TASK:'):
                    current_result['task'] = line.split(':', 1)[1].strip()
                # Handle single separator
                elif line.startswith('-'):
                    collecting_output = not collecting_output
                    continue
                # Collect solver output (only between single separators)
                elif collecting_output and line:
                    solver_output.append(line)
    
    except Exception as e:
        print(f"Error parsing log file {log_file}: {e}")
    
    # Add the last result
    if current_file and current_result:
        current_result['solver_output'] = '\n'.join(solver_output)
        results[current_file] = current_result
    
    return results

def update_excel(excel_file, results, task_name, output_file):
    """Update Excel file with solver results."""
    try:
        # Read the Excel file
        df = pd.read_excel(excel_file)
        
        # Add new columns if they don't exist
        result_col = f'res_{task_name}_result'
        time_col = f'res_{task_name}_time'
        reason_col = f'res_{task_name}_reason'
        
        if result_col not in df.columns:
            df[result_col] = ''
        if time_col not in df.columns:
            df[time_col] = ''
        if reason_col not in df.columns:
            df[reason_col] = ''
        
        # Update results for each file
        for index, row in df.iterrows():
            file_name = row['file_name']
            if file_name in results:
                result = results[file_name]
                df.at[index, result_col] = result.get('result', '')
                df.at[index, time_col] = result.get('time', '')
                df.at[index, reason_col] = result.get('solver_output', '')
        
        # Create output directory if it doesn't exist
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        
        # Save updated Excel file
        with pd.ExcelWriter(output_file, engine='openpyxl', mode='a' if os.path.exists(output_file) else 'w') as writer:
            df.to_excel(writer, index=False, sheet_name='SMT2 Analysis')
            
            # Adjust column widths and enable text wrapping
            worksheet = writer.sheets['SMT2 Analysis']
            for i, col in enumerate(df.columns):
                # Calculate column width with a maximum limit
                column_width = min(max(df[col].astype(str).map(len).max(), len(col)) * 1.2 + 10, 100)
                worksheet.column_dimensions[chr(65 + i)].width = column_width
                
                # Enable text wrapping for the reason column
                if col == reason_col:
                    for cell in worksheet[chr(65 + i)][1:]:  # Skip header row
                        cell.alignment = openpyxl.styles.Alignment(wrap_text=True)
        
        print(f"Excel file updated successfully: {output_file}")
        
    except Exception as e:
        print(f"Error updating Excel file: {e}")

def process_log_directory(log_dir):
    """Process a single log directory and return results and task name."""
    results = {}
    task_name = None
    
    # Get all log files
    log_files = [f for f in os.listdir(log_dir) if f.startswith('batch_') and f.endswith('_results.log')]
    
    # Process each log file with progress bar
    for log_file in tqdm(log_files, desc="Processing log files", unit="file"):
        log_path = os.path.join(log_dir, log_file)
        
        # Extract task name from the first log file
        if task_name is None:
            task_name = extract_task_name(log_path)
            if not task_name:
                print(f"Error: Could not determine task name from log files in {log_dir}")
                continue
        
        batch_results = parse_log_file(log_path)
        results.update(batch_results)
    
    return results, task_name

def main():
    # Parse command line arguments
    args = parse_args()
    
    # Validate input file exists
    if not os.path.exists(args.input_excel):
        print(f"Error: Excel file not found: {args.input_excel}")
        sys.exit(1)
    
    print(f"Processing configuration:")
    print(f"  Input Excel: {args.input_excel}")
    print(f"  Log directories: {', '.join(args.log_dir)}")
    print(f"  Output file: {args.output_file}")
    
    # Read the initial Excel file
    df = pd.read_excel(args.input_excel)
    
    # Process all log directories
    for log_dir in args.log_dir:
        # Check if log directory exists
        if not os.path.exists(log_dir):
            print(f"Warning: Log directory not found, skipping: {log_dir}")
            continue
            
        # Check if log directory is empty
        if not os.listdir(log_dir):
            print(f"Warning: Log directory is empty, skipping: {log_dir}")
            continue
            
        results, task_name = process_log_directory(log_dir)
        
        if results and task_name:
            # Add new columns if they don't exist
            result_col = f'res_{task_name}_result'
            time_col = f'res_{task_name}_time'
            reason_col = f'res_{task_name}_reason'
            
            if result_col not in df.columns:
                df[result_col] = ''
            if time_col not in df.columns:
                df[time_col] = ''
            if reason_col not in df.columns:
                df[reason_col] = ''
            
            # Update results for each file
            for index, row in df.iterrows():
                file_name = row['file_name']
                if file_name in results:
                    result = results[file_name]
                    df.at[index, result_col] = result.get('result', '')
                    df.at[index, time_col] = result.get('time', '')
                    df.at[index, reason_col] = result.get('solver_output', '')
            
            print(f"\nProcessed {len(results)} results for task {task_name}")
        else:
            print(f"\nNo results found in log directory: {log_dir}")
    
    # Create output directory if it doesn't exist
    os.makedirs(os.path.dirname(args.output_file), exist_ok=True)
    
    # Save the final Excel file with all results
    with pd.ExcelWriter(args.output_file, engine='openpyxl', mode='w') as writer:
        df.to_excel(writer, index=False, sheet_name='SMT2 Analysis')
        
        # Adjust column widths and enable text wrapping
        worksheet = writer.sheets['SMT2 Analysis']
        for i, col in enumerate(df.columns):
            # Calculate column width with a maximum limit
            column_width = min(max(df[col].astype(str).map(len).max(), len(col)) * 1.2 + 10, 100)
            worksheet.column_dimensions[chr(65 + i)].width = column_width
            
            # Enable text wrapping for all reason columns
            if col.endswith('_reason'):
                for cell in worksheet[chr(65 + i)][1:]:  # Skip header row
                    cell.alignment = openpyxl.styles.Alignment(wrap_text=True)
    
    print(f"\nExcel file updated successfully: {args.output_file}")

if __name__ == "__main__":
    main() 