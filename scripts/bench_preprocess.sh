#!/bin/bash

# Default values
INPUT_DIR=""
PROCESS_SCRIPT=""
OUTPUT_DIR=""
LOG_DIR=""
LOG_FILE=""
TIMEOUT=10  # Default timeout in seconds
EXCEL_DIR="charts"  # Default directory for Excel files
EXCEL_FILE="smt2_analysis.xlsx"  # Default Excel file name

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --input-dir)
            INPUT_DIR="$2"
            shift 2
            ;;
        --process-script)
            PROCESS_SCRIPT="$2"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --log-dir)
            LOG_DIR="$2"
            shift 2
            ;;
        --log-file)
            LOG_FILE="$2"
            shift 2
            ;;
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        --excel-dir)
            EXCEL_DIR="$2"
            shift 2
            ;;
        --excel-file)
            EXCEL_FILE="$2"
            shift 2
            ;;
        *)
            echo "Unknown parameter: $1"
            echo "Usage: $0 --input-dir <input_benchmark_dir> [--process-script <processing_script>] [--output-dir <output_dir>] [--log-dir <log_dir>] [--log-file <log_file>] [--timeout <seconds>] [--excel-dir <excel_dir>] [--excel-file <excel_file>]"
            echo "Example: $0 --input-dir Norn --process-script scripts/preprocess.py --output-dir Norn-preprocessed --log-dir results/preprocess --log-file Norn-preprocess.log --excel-dir charts --excel-file Norn_base.xlsx"
            exit 1
            ;;
    esac
done

# Check if required input directory is provided
if [ -z "$INPUT_DIR" ]; then
    echo "Error: Missing required argument --input-dir"
    echo "Usage: $0 --input-dir <input_benchmark_dir> [--process-script <processing_script>] [--output-dir <output_dir>] [--log-dir <log_dir>] [--log-file <log_file>] [--timeout <seconds>] [--excel-dir <excel_dir>] [--excel-file <excel_file>]"
    echo "Example: $0 --input-dir Norn --process-script scripts/preprocess.py --output-dir Norn-preprocessed --log-dir results/preprocess --log-file Norn-preprocess.log --excel-dir charts --excel-file Norn_base.xlsx"
    exit 1
fi

# If process-script is provided, check if log parameters are also provided
if [ ! -z "$PROCESS_SCRIPT" ]; then
    if [ -z "$LOG_DIR" ] || [ -z "$LOG_FILE" ]; then
        echo "Error: When --process-script is provided, both --log-dir and --log-file are required"
        exit 1
    fi
fi

# Get absolute paths of input arguments
INPUT_DIR=$(realpath "$INPUT_DIR")
if [ ! -z "$PROCESS_SCRIPT" ]; then
    PROCESS_SCRIPT=$(realpath "$PROCESS_SCRIPT")
fi
if [ ! -z "$OUTPUT_DIR" ]; then
    OUTPUT_DIR=$(realpath "$OUTPUT_DIR")
fi
if [ ! -z "$LOG_DIR" ] && [ ! -z "$LOG_FILE" ]; then
    LOG_DIR=$(realpath "$LOG_DIR")
    LOG_FILE="$LOG_DIR/$LOG_FILE"
    # Create log directory if it doesn't exist
    mkdir -p "$LOG_DIR"
    # Create or truncate the log file
    : > "$LOG_FILE"
    echo "Log file created and cleared: $LOG_FILE"
fi

# Check if input directory exists
if [ ! -d "$INPUT_DIR" ]; then
    echo "Error: Input directory does not exist: $INPUT_DIR"
    exit 1
fi

# Check if processing script exists if provided
if [ ! -z "$PROCESS_SCRIPT" ] && [ ! -f "$PROCESS_SCRIPT" ]; then
    echo "Error: Processing script does not exist: $PROCESS_SCRIPT"
    exit 1
fi

# Create output directory if it doesn't exist and if output directory is provided
if [ ! -z "$OUTPUT_DIR" ]; then
    mkdir -p "$OUTPUT_DIR"
fi

# Create Excel directory if it doesn't exist
mkdir -p "$EXCEL_DIR"

# Function to print separators
print_double_separator() {
    if [ ! -z "$LOG_FILE" ]; then
        echo "===========================================================" >> "$LOG_FILE"
    fi
}

print_single_separator() {
    if [ ! -z "$LOG_FILE" ]; then
        echo "-----------------------------------------------------------" >> "$LOG_FILE"
    fi
}

# Step 1: Run initial benchmark analysis
echo "Running initial benchmark analysis..."
python scripts/analysis_benchmarks.py --input-dir "$INPUT_DIR" --output-dir "$EXCEL_DIR" --output-file "$EXCEL_FILE"
echo "Initial analysis saved in: $EXCEL_DIR/$EXCEL_FILE"

# Step 2: Process all .smt2 files recursively if process script is provided
if [ ! -z "$PROCESS_SCRIPT" ]; then
    echo "Starting preprocessing..."
    find "$INPUT_DIR" -type f -name "*.smt2" | sort -V | while read -r input_file; do
        # Get relative path to maintain directory structure
        rel_path=${input_file#$INPUT_DIR/}
        # Create output directory structure
        output_subdir="$OUTPUT_DIR/$(dirname "$rel_path")"
        mkdir -p "$output_subdir"
        
        # Get output file path
        output_file="$output_subdir/$(basename "$input_file")"
        
        echo "Processing: $input_file"
        
        if [ ! -z "$LOG_FILE" ]; then
            print_double_separator
            echo "FILE: $(basename "$input_file")" >> "$LOG_FILE"
            echo "PATH: $input_file" >> "$LOG_FILE"
            echo "OUTPUT: $output_file" >> "$LOG_FILE"
            echo "SCRIPT: $(basename "$PROCESS_SCRIPT")" >> "$LOG_FILE"
            echo "TIMEOUT: ${TIMEOUT}s" >> "$LOG_FILE"
            print_single_separator
            
            # Record start time in seconds since epoch
            START_TIME=$(date +%s.%N)
            
            # Create a temporary file for script output
            TEMP_OUTPUT=$(mktemp)
            
            # Run the processing script with timeout and capture the output
            timeout "${TIMEOUT}s" python "$PROCESS_SCRIPT" "$input_file" "$output_file" > "$TEMP_OUTPUT" 2>&1
            
            # Capture exit status
            STATUS=$?
            
            # Record end time in seconds since epoch
            END_TIME=$(date +%s.%N)
            
            # Calculate processing time
            PROCESSING_TIME=$(echo "$END_TIME - $START_TIME" | bc)
            
            # Write script output to the log file
            cat "$TEMP_OUTPUT" >> "$LOG_FILE"
            rm -f "$TEMP_OUTPUT"
            
            print_single_separator
            echo "PROCESSING_TIME: $PROCESSING_TIME" >> "$LOG_FILE"
            
            # Determine the result based on exit status
            if [ $STATUS -eq 124 ] || [ $STATUS -eq 137 ]; then
                echo "RESULT: TIMEOUT" >> "$LOG_FILE"
                # Remove the output file if it was created during timeout
                rm -f "$output_file"
            elif [ $STATUS -eq 0 ]; then
                # Check if the output file exists and is not empty
                if [ -f "$output_file" ] && [ -s "$output_file" ]; then
                    echo "RESULT: SUCCESS" >> "$LOG_FILE"
                else
                    echo "RESULT: ERROR (Empty or missing output file)" >> "$LOG_FILE"
                    rm -f "$output_file"
                fi
            else
                echo "RESULT: ERROR" >> "$LOG_FILE"
                # Remove the output file if it was created during error
                rm -f "$output_file"
            fi
        else
            timeout "${TIMEOUT}s" python "$PROCESS_SCRIPT" -v "$input_file" "$output_file"
            STATUS=$?
            if [ $STATUS -eq 124 ] || [ $STATUS -eq 137 ]; then
                echo "Timeout processing: $input_file"
                rm -f "$output_file"
            elif [ $STATUS -ne 0 ]; then
                echo "Error processing: $input_file (Exit code: $STATUS)"
                rm -f "$output_file"
            fi
        fi
    done

    # Step 3: Run preprocessing analysis only if process script was provided
    if [ ! -z "$LOG_FILE" ]; then
        echo "Running preprocessing analysis..."
        python scripts/analysis_preprocess.py --input-excel "$EXCEL_DIR/$EXCEL_FILE" --input-log "$LOG_FILE" --output-file "$EXCEL_DIR/$EXCEL_FILE"
        echo "Preprocessing analysis saved in: $EXCEL_DIR/$EXCEL_FILE"
    fi
fi

echo "Processing complete."
if [ ! -z "$OUTPUT_DIR" ]; then
    echo "Results saved in: $OUTPUT_DIR"
fi
if [ ! -z "$LOG_FILE" ]; then
    echo "Log file saved in: $LOG_FILE"
fi
echo "Excel report: $EXCEL_DIR/$EXCEL_FILE" 