#!/bin/bash
InputRunNumber=$1
# DatDataPath="/eos/user/s/shunlian/AHCAL/data/stable_7_17/"
DatDataPath="/eos/user/y/yanghe/AHCAL_data/"
# DatDataPath="/eos/user/y/ymaruya/FASER/AHCAL-data/"
get_run_file() {
    local run_number=$1
    local file=$(ls ${DatDataPath}AHCAL_Run${run_number}_*.dat 2>/dev/null | head -n 1)
    if [[ -n "$file" ]]; then
        echo "$file"
    else
        echo "No file found for RunNumber $run_number" >&2
        return 1
    fi
}

if [ -z "$InputRunNumber" ]; then
    echo "Usage: $0 <RunNumber>"
fi
echo "Processing Run Number: $InputRunNumber"

if [ ! -d "$DatDataPath" ]; then
    echo "Data path does not exist: $DatDataPath"
fi

# check the data file exists
filename=$(get_run_file "$InputRunNumber")
if [ $? -ne 0 ]; then
    echo "Error: Could not find data file for RunNumber $InputRunNumber"
    exit 2
fi
echo "Found data file: $filename"

# Run the analysis script
echo "Running analysis script..."
source /cvmfs/sft.cern.ch/lcg/views/LCG_105/x86_64-el9-gcc12-opt/setup.sh
PWD=$(pwd)
cd /eos/user/y/ymaruya/FASER/hbuana/config/
echo "$filename" > list_cosmic.txt
../bin/hbuana -c config.yaml

if [ $? -ne 0 ]; then
    echo "Error: Analysis script failed"
    exit 2
fi
echo "Analysis completed successfully."
cd "$PWD"





