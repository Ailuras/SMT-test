#!/bin/bash

# This script kills all related processes including batch processes and solver processes
# Usage: kill.sh [--log-dir <log_dir>] [--log-file <log_file>]

# Default values
LOG_DIR=""
LOG_FILE=""

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
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
            echo "Usage: $0 [--log-dir <log_dir>] [--log-file <log_file>]"
            exit 1
            ;;
    esac
done

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

echo "Searching for processes to terminate..."

# Function to kill processes with logging
kill_processes() {
    local pattern=$1
    local name=$2
    local count=$(pgrep -f "$pattern" | wc -l)
    
    if [ "$count" -gt 0 ]; then
        echo "Found $count $name process(es)"
        echo "Terminating $name processes..."
        pkill -f "$pattern"
        sleep 1
        
        # Check if any processes are still running
        if pgrep -f "$pattern" > /dev/null; then
            echo "Warning: Some $name processes are still running. Forcing termination..."
            pkill -9 -f "$pattern"
            sleep 1
            
            # Final check
            if pgrep -f "$pattern" > /dev/null; then
                echo "Error: Failed to terminate all $name processes"
                return 1
            else
                echo "Successfully terminated all $name processes"
            fi
        else
            echo "Successfully terminated all $name processes"
        fi
    else
        echo "No $name processes found"
    fi
    return 0
}

# Kill processes in order
echo "Terminating processes in order..."

# 1. Kill batch processes
kill_processes "batch.sh" "batch processing"

# 2. Kill solver processes
kill_processes "cvc5" "CVC5 solver"
kill_processes "z3" "Z3 solver"
kill_processes "z3-noodler" "Z3-Noodler solver"

# 3. Kill run.sh processes
kill_processes "run.sh" "solver runner"

# 4. Kill Python analysis processes
kill_processes "analysis_solve.py" "Python analysis"
kill_processes "analysis_preprocess.py" "Python preprocessing"

echo "Process termination complete." 