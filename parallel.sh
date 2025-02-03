#!/bin/bash

group_directory="paths/solved"
result_directory="results//solved"
timeout=1200
num_groups=8
base_dir="benchmarks"

mkdir -p "$group_directory"
mkdir -p "$result_directory"
rm -rf "$group_directory"/*
rm -rf "$result_directory"/*

smt2_files=$(find "$base_dir" -type f -name "*.smt2" | sort -V)

total_files=$(wc -l <<< "$smt2_files")

split -l $((($total_files + num_groups - 1) / num_groups)) \
  <(echo "$smt2_files") "${group_directory}/group_"

for group_file in "${group_directory}/group_"*; do
  group_name=$(basename "$group_file")
  nohup ./run.sh "$group_file" "$timeout" > "${result_directory}/${group_name}.log" 2>&1 &
done
