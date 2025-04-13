#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
SMT2 Files Analysis Script
This script analyzes SMT2 files from a specific folder and creates an Excel report with their metadata.
"""

import os
import re
import pandas as pd
import argparse
from pathlib import Path
import natsort

def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(description='Analyze SMT2 files and create an Excel report.')
    parser.add_argument('--input-dir', required=True, help='Directory containing SMT2 files')
    parser.add_argument('--output-dir', default='charts', help='Directory to save the Excel report')
    parser.add_argument('--output-file', default='smt2_analysis.xlsx', help='Name of the output Excel file')
    
    return parser.parse_args()

def extract_metadata(file_path):
    """Extract metadata from an SMT2 file."""
    metadata = {
        "file_name": os.path.basename(file_path),
        "path": file_path,
        "theory": "",
        "category": "",
        "status": "",
        "target": ""
    }
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            
            # Extract logic/theory
            logic_match = re.search(r'\(set-logic\s+([^\)]+)\)', content)
            if logic_match:
                metadata["theory"] = logic_match.group(1).strip()
            
            # Extract category
            category_match = re.search(r'\(set-info\s+:category\s+"([^"]+)"\)', content)
            if category_match:
                metadata["category"] = category_match.group(1).strip()
            
            # Extract status
            status_match = re.search(r'\(set-info\s+:status\s+([^\)]+)\)', content)
            if status_match:
                metadata["status"] = status_match.group(1).strip()
            
            # Extract target
            target_match = re.search(r'Target solver:\s*([^\n\r,.]+)', content)
            if target_match:
                metadata["target"] = target_match.group(1).strip()
            
    except Exception as e:
        print(f"Error processing {file_path}: {e}")
    
    return metadata

def process_smt2_files(input_dir):
    """Process all SMT2 files in the input directory and its subdirectories."""
    all_data = []
    
    # Get all SMT2 files recursively and sort them naturally
    try:
        smt2_files = []
        for root, _, files in os.walk(input_dir):
            for file in files:
                if file.endswith('.smt2'):
                    smt2_files.append(os.path.join(root, file))
        smt2_files = natsort.natsorted(smt2_files)  # Natural sort the files
        print(f"Found {len(smt2_files)} SMT2 files")
    except FileNotFoundError:
        print(f"Input directory {input_dir} not found!")
        return []
    
    # Process each file
    for file_path in smt2_files:
        metadata = extract_metadata(file_path)
        all_data.append(metadata)
    
    return all_data

def create_excel_report(data, output_file):
    """Create an Excel report with the extracted data."""
    if not data:
        print("No data to write to Excel!")
        return
        
    # Create a DataFrame from the extracted data
    df = pd.DataFrame(data)
    
    # Add empty columns for future results
    # For res_preprocess (now first)
    df["res_preprocess_result"] = ""
    df["res_preprocess_time"] = ""
    df["res_preprocess_reason"] = ""
    
    # Save to Excel
    try:
        with pd.ExcelWriter(output_file, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='SMT2 Analysis')
            
            # Adjust column widths
            worksheet = writer.sheets['SMT2 Analysis']
            for i, col in enumerate(df.columns):
                column_width = min(max(df[col].astype(str).map(len).max(), len(col)) * 1.2 + 10, 100)
                worksheet.column_dimensions[chr(65 + i)].width = column_width
        
        print(f"Excel report saved to: {output_file}")
    except Exception as e:
        print(f"Error creating Excel file: {e}")

if __name__ == "__main__":
    args = parse_args()
    
    # Create output directory if it doesn't exist
    os.makedirs(args.output_dir, exist_ok=True)
    
    # Construct full output file path
    output_file = os.path.join(args.output_dir, args.output_file)
    
    print(f"Processing SMT2 files from: {args.input_dir}")
    data = process_smt2_files(args.input_dir)
    create_excel_report(data, output_file)
    print("Analysis complete!") 