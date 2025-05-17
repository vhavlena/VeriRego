#!/bin/bash

# Get the root directory from command line argument, default to current directory
root_dir="${1:-.}"

# Output file where all results will be stored
output_file="rego_analysis_results.txt"

# Clear the output file if it exists
> "$output_file"

# Find all .rego files recursively from the specified directory and analyze each one
find "$root_dir" -type f -name "*.rego" | while read -r policy_file; do
    echo "Analyzing: $policy_file" >> "$output_file"
    echo "----------------------------------------" >> "$output_file"
    ./rego_analyzer "$policy_file" >> "$output_file" 2>&1
    echo -e "\n" >> "$output_file"
done

echo "Analysis complete. Results stored in $output_file"
