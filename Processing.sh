#!/bin/bash
#
# File: Processing.sh
# Author: ymaruya
# Date: $(date +%Y-%m-%d)
# Description: Process root files for layer 38 problem analysis
#
# Usage: ./Processing.sh [options]
#
mkdir -p layer38problem
cd layer38problem

for file in $(ls -1 /eos/home-y/ymaruya/FASER/AHCAL-data/layer38problem/*.root)
do
    echo "Processing $file"
    # Extract the filename without the path
    filename=$(basename "$file" .root)
    
    # Create directory if it doesn't exist
    mkdir -p "$filename"
    
    # Change to the directory and process the file
    (cd "$filename" && 
    #  ../../bin/Test "$file" ../../calibration/pedestal.root ../../calibration/dac.root ../../calibration/mip.root test_"$filename".root &&
     ../../bin/ForMuon_eff "$file" ../../calibration/pedestal.root ../../calibration/dac.root ../../calibration/mip.root muon_"$filename".root 14 34 &&
     echo "Processed $file into test_$filename.root")
done

cd ..
echo "All files processed."

