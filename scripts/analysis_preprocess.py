#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Process Preprocessing Results Script
This script processes preprocessing results from log files and updates the Excel report.

Usage:
    python analysis_preprocess.py --input-excel <excel_file> --input-log <log_file> --output-file <output_file>
    
Example:
    python analysis_preprocess.py --input-excel charts/smt2_analysis.xlsx --input-log results/preprocess/Norn-preprocess.log --output-file charts/smt2_analysis_preprocessed.xlsx
"""

import os
import re
import sys
import pandas as pd
import argparse
from pathlib import Path
import openpyxl

def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(description='Process preprocessing results and update Excel report.')
    parser.add_argument('--input-excel', required=True, help='Input Excel file containing benchmark information')
    parser.add_argument('--input-log', required=True, help='Input log file containing preprocessing results')
    parser.add_argument('--output-file', required=True, help='Output Excel file to save updated results')
    
    return parser.parse_args()

def parse_log_file(log_file):
    """Parse a log file and extract results for each file."""
    results = {}
    current_file = None
    current_result = {}
    script_output = []
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
                        current_result['script_output'] = '\n'.join(script_output)
                        results[current_file] = current_result
                    current_file = line.split(':', 1)[1].strip()
                    current_result = {}
                    script_output = []
                    collecting_output = False
                
                # Parse result information
                elif line.startswith('RESULT:'):
                    current_result['result'] = line.split(':', 1)[1].strip()
                elif line.startswith('PROCESSING_TIME:'):
                    current_result['time'] = float(line.split(':', 1)[1].strip())
                # Handle single separator
                elif line.startswith('-'):
                    collecting_output = not collecting_output
                    continue
                # Collect script output (only between single separators)
                elif collecting_output and line:
                    script_output.append(line)
    
    except Exception as e:
        print(f"Error parsing log file {log_file}: {e}")
    
    # Add the last result
    if current_file and current_result:
        current_result['script_output'] = '\n'.join(script_output)
        results[current_file] = current_result
    
    return results

def update_excel(excel_file, results, output_file):
    """Update Excel file with preprocessing results."""
    try:
        # Read the Excel file
        df = pd.read_excel(excel_file)
        
        # Update results for each file
        for index, row in df.iterrows():
            file_name = row['file_name']
            if file_name in results:
                result = results[file_name]
                df.at[index, 'res_preprocess_result'] = result.get('result', '')
                df.at[index, 'res_preprocess_time'] = result.get('time', '')
                df.at[index, 'res_preprocess_reason'] = result.get('script_output', '')
        
        # Create output directory if it doesn't exist
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        
        # Save updated Excel file
        with pd.ExcelWriter(output_file, engine='openpyxl', mode='w') as writer:
            df.to_excel(writer, index=False, sheet_name='SMT2 Analysis')
            
            # Adjust column widths and enable text wrapping
            worksheet = writer.sheets['SMT2 Analysis']
            for i, col in enumerate(df.columns):
                # Calculate column width with a maximum limit
                column_width = min(max(df[col].astype(str).map(len).max(), len(col)) * 1.2 + 10, 100)
                worksheet.column_dimensions[chr(65 + i)].width = column_width
                
                # Enable text wrapping for the reason column
                if col == 'res_preprocess_reason':
                    for cell in worksheet[chr(65 + i)][1:]:  # Skip header row
                        cell.alignment = openpyxl.styles.Alignment(wrap_text=True)
        
        print(f"Excel file updated successfully: {output_file}")
        
    except Exception as e:
        print(f"Error updating Excel file: {e}")

def main():
    # Parse command line arguments
    args = parse_args()
    
    # Validate input file exists
    if not os.path.exists(args.input_excel):
        print(f"Error: Excel file not found: {args.input_excel}")
        sys.exit(1)
    
    # Validate log file exists
    if not os.path.exists(args.input_log):
        print(f"Error: Log file not found: {args.input_log}")
        sys.exit(1)
    
    print(f"Processing preprocessing results from: {args.input_log}")
    print(f"Input Excel file: {args.input_excel}")
    print(f"Output Excel file: {args.output_file}")
    
    # Process log file
    results = parse_log_file(args.input_log)
    
    # Update Excel file
    if results:
        update_excel(args.input_excel, results, args.output_file)
        print(f"Processed {len(results)} results")
    else:
        print("No results found to process")

if __name__ == "__main__":
    main()
