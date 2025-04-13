#!/bin/bash

# This script processes files in parallel batches
# Usage: bench_solve.sh --input-dir <input_dir> --output-dir <output_dir> --task <task_name> --solver <solver_name> --timeout <timeout> [--parallel <num_parallel>] [--excel-dir <excel_dir>] [--excel-file <excel_file>] [--log-dir <log_dir>] [--log-file <log_file>]

# Function to handle cleanup on script termination
cleanup() {
    echo "Script interrupted. Cleaning up..."
    # Kill all background processes
    for pid in "${PIDS[@]}"; do
        if ps -p "$pid" > /dev/null; then
            kill "$pid" 2>/dev/null
        fi
    done
    # Wait for all processes to finish
    wait
    # Generate Excel file if needed
    if [ ! -z "$EXCEL_DIR" ] && [ ! -z "$EXCEL_FILE" ]; then
        echo "Processing results for Excel report..."
        EXCEL_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/$EXCEL_DIR/$EXCEL_FILE"
        OUTPUT_EXCEL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/$EXCEL_DIR/${EXCEL_FILE%.*}_${TASK_NAME}.xlsx"
        if [ -f "$EXCEL_PATH" ]; then
            python "$PARALLEL_SCRIPT_DIR/analysis_solve.py" \
                --input-excel "$EXCEL_PATH" \
                --log-dir "$TASK_OUTPUT_DIR" \
                --output-file "$OUTPUT_EXCEL"
            echo "Results processed and saved to: $OUTPUT_EXCEL"
        fi
    fi
    exit 0
}

# Set up signal handlers
trap cleanup SIGINT SIGTERM

# Default values
INPUT_DIR=""
OUTPUT_DIR=""
TASK_NAME=""
SOLVER_NAME=""
TIMEOUT=10
NUM_PARALLEL=1
EXCEL_DIR=""
EXCEL_FILE=""
LOG_DIR=""
LOG_FILE=""

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --input-dir)
            INPUT_DIR="$2"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --task)
            TASK_NAME="$2"
            shift 2
            ;;
        --solver)
            SOLVER_NAME="$2"
            shift 2
            ;;
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        --parallel)
            NUM_PARALLEL="$2"
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
        --log-dir)
            LOG_DIR="$2"
            shift 2
            ;;
        --log-file)
            LOG_FILE="$2"
            shift 2
            ;;
        *)
            echo "Unknown parameter: $1"
            echo "Usage: $0 --input-dir <input_dir> --output-dir <output_dir> --task <task_name> --solver <solver_name> --timeout <timeout> [--parallel <num_parallel>] [--excel-dir <excel_dir>] [--excel-file <excel_file>] [--log-dir <log_dir>] [--log-file <log_file>]"
            echo "  --input-dir: Directory containing .smt2 files to process"
            echo "  --output-dir: Directory to save results"
            echo "  --task: Name of the task (e.g., cvc5, cvc5-preprocess)"
            echo "  --solver: Solver to use (cvc5, z3, or z3-noodler)"
            echo "  --timeout: Timeout in seconds for each file"
            echo "  --parallel: Optional - Number of parallel processes (default: number of CPU cores)"
            echo "  --excel-dir: Directory to save Excel report"
            echo "  --excel-file: Excel file name"
            echo "  --log-dir: Directory to save main process log"
            echo "  --log-file: Main process log file name"
            exit 1
            ;;
    esac
done

# Check if all required arguments are provided
if [ -z "$INPUT_DIR" ] || [ -z "$OUTPUT_DIR" ] || [ -z "$TASK_NAME" ] || [ -z "$SOLVER_NAME" ]; then
    echo "Error: Missing required arguments"
    echo "Usage: $0 --input-dir <input_dir> --output-dir <output_dir> --task <task_name> --solver <solver_name> --timeout <timeout> [--parallel <num_parallel>] [--excel-dir <excel_dir>] [--excel-file <excel_file>] [--log-dir <log_dir>] [--log-file <log_file>]"
    echo "  --input-dir: Directory containing .smt2 files to process"
    echo "  --output-dir: Directory to save results"
    echo "  --task: Name of the task (e.g., cvc5, cvc5-preprocess)"
    echo "  --solver: Solver to use (cvc5, z3, or z3-noodler)"
    echo "  --timeout: Timeout in seconds for each file"
    echo "  --parallel: Optional - Number of parallel processes (default: number of CPU cores)"
    echo "  --excel-dir: Directory to save Excel report"
    echo "  --excel-file: Excel file name"
    echo "  --log-dir: Directory to save main process log"
    echo "  --log-file: Main process log file name"
    exit 1
fi

# Get absolute paths for both scripts
PARALLEL_SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BATCH_SCRIPT="$PARALLEL_SCRIPT_DIR/batch.sh"

# Check if batch script exists
if [ ! -f "$BATCH_SCRIPT" ]; then
    echo "Error: Batch processing script not found: $BATCH_SCRIPT"
    exit 1
fi

# Make batch script executable
chmod +x "$BATCH_SCRIPT"

# Get absolute paths
INPUT_DIR=$(realpath "$INPUT_DIR")
OUTPUT_DIR=$(realpath "$OUTPUT_DIR")

# Set up logging if log directory and file are provided
if [ ! -z "$LOG_DIR" ] && [ ! -z "$LOG_FILE" ]; then
    LOG_DIR=$(realpath "$LOG_DIR")
    LOG_FILE="$LOG_DIR/$LOG_FILE"
    mkdir -p "$LOG_DIR"
    # Create or truncate the log file
    : > "$LOG_FILE"
    exec 1> >(tee -a "$LOG_FILE")
    exec 2>&1
    echo "Log file created: $LOG_FILE"
fi

# Set the number of parallel processes
if [ -z "$NUM_PARALLEL" ]; then
    # Use the number of CPU cores as default
    NUM_PARALLEL=$(nproc)
fi

# Validate solver name
if [ "$SOLVER_NAME" != "cvc5" ] && [ "$SOLVER_NAME" != "z3" ] && [ "$SOLVER_NAME" != "z3-noodler" ]; then
    echo "Error: Invalid solver name. Choose either 'cvc5', 'z3', or 'z3-noodler'."
    exit 1
fi

# Set solver path based on solver name
SOLVER_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/solvers/$SOLVER_NAME/run.sh"

# Check if input directory exists
if [ ! -d "$INPUT_DIR" ]; then
    echo "Error: Input directory does not exist: $INPUT_DIR"
    exit 1
fi

# Check if solver exists
if [ ! -f "$SOLVER_PATH" ]; then
    echo "Error: Solver does not exist: $SOLVER_PATH"
    exit 1
fi

# Make solver executable if it's not already
chmod +x "$SOLVER_PATH"

# Create task-specific output directory
TASK_OUTPUT_DIR="$OUTPUT_DIR/$TASK_NAME"
mkdir -p "$TASK_OUTPUT_DIR"

# Find all .smt2 files in the input directory
FILES=($(find "$INPUT_DIR" -type f -name "*.smt2"))
TOTAL_FILES=${#FILES[@]}

if [ "$TOTAL_FILES" -eq 0 ]; then
    echo "Error: No smt2 files found in: $INPUT_DIR"
    exit 1
fi

echo "Processing configuration:"
echo "  Input directory: $INPUT_DIR"
echo "  Output directory: $TASK_OUTPUT_DIR"
echo "  Task: $TASK_NAME"
echo "  Solver: $SOLVER_NAME"
echo "  Timeout: ${TIMEOUT}s"
echo "  Parallel processes: $NUM_PARALLEL"
echo "  Total files: $TOTAL_FILES"

# Calculate batch size (number of files per batch)
# Each batch will be processed serially by a single process
BATCH_SIZE=$(( (TOTAL_FILES + NUM_PARALLEL - 1) / NUM_PARALLEL ))
if [ "$BATCH_SIZE" -eq 0 ]; then
    BATCH_SIZE=1
fi

echo "  Files per batch: $BATCH_SIZE"

# Process files in parallel batches
echo "Starting parallel processing with $NUM_PARALLEL processes..."
for ((i=0; i<NUM_PARALLEL; i++)); do
    # Calculate start and end indices for this batch
    START=$((i * BATCH_SIZE))
    END=$(( (i+1) * BATCH_SIZE - 1 ))
    
    # Ensure end index doesn't exceed total files
    if [ "$END" -ge "$TOTAL_FILES" ]; then
        END=$((TOTAL_FILES - 1))
    fi
    
    # Skip empty batches
    if [ "$START" -gt "$END" ]; then
        continue
    fi
    
    # Create a list of files for this batch
    BATCH_FILES=()
    for ((j=START; j<=END; j++)); do
        BATCH_FILES+=("${FILES[j]}")
    done
    
    # Create batch output file
    BATCH_OUTPUT="$TASK_OUTPUT_DIR/batch_${i}_${SOLVER_NAME}_results.log"
    
    # Ensure output file is empty before starting
    : > "$BATCH_OUTPUT"
    
    # Run batch_process.sh in background with nohup, redirecting output to /dev/null
    nohup "$BATCH_SCRIPT" --solver-path "$SOLVER_PATH" --timeout "$TIMEOUT" --output-file "$BATCH_OUTPUT" --task "$TASK_NAME" --files "${BATCH_FILES[@]}" > /dev/null 2>&1 &
    
    # Store process ID
    PIDS[$i]=$!
    echo "Started batch $i with PID ${PIDS[$i]}"
done

# Wait for all processes to complete
echo "Waiting for all processes to complete..."
for pid in "${PIDS[@]}"; do
    wait "$pid"
done

echo "All processing complete. Results saved in: $TASK_OUTPUT_DIR"

# If provided Excel directory and file name, automatically process results
if [ ! -z "$EXCEL_DIR" ] && [ ! -z "$EXCEL_FILE" ]; then
    echo "Processing results for Excel report..."
    
    # Get absolute path for Excel file
    EXCEL_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/$EXCEL_DIR/$EXCEL_FILE"
    OUTPUT_EXCEL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/$EXCEL_DIR/${EXCEL_FILE%.*}_${TASK_NAME}.xlsx"
    
    # Check if input Excel file exists
    if [ ! -f "$EXCEL_PATH" ]; then
        echo "Error: Input Excel file not found: $EXCEL_PATH"
        exit 1
    fi
    
    # Run analysis_solve.py to process results
    python "$PARALLEL_SCRIPT_DIR/analysis_solve.py" \
        --input-excel "$EXCEL_PATH" \
        --log-dir "$TASK_OUTPUT_DIR" \
        --output-file "$OUTPUT_EXCEL"
    
    echo "Results processed and saved to: $OUTPUT_EXCEL"
fi
