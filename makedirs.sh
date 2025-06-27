#!/bin/bash
#
# File: dump.sh
# Author: ymaruya
# Date: $(date +%Y-%m-%d)
# Description: [Brief description of what this script does]
#
# Usage: ./dump.sh [options]
#
cd layer38problem
for file in $(ls -1 ../../AHCAL-data/layer38problem/*.dat)
do
    echo "Processing $file"
    # Extract the filename without the path
    mkdir "$(basename "$file" .dat)"
done

