#!/bin/bash
InputRunNumber=$1
DatDataPath="/afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-data/"
get_run_file() {
    local run_number=$1
    local file=$(ls ${DatDataPath}AHCAL_Run${run_number}_*.root 2>/dev/null | head -n 1)
    if [[ -n "$file" ]]; then
        echo "$file"
    else
        echo "No file found for RunNumber $run_number" >&2
        return 1
    fi
}
if [ -z "$InputRunNumber" ]; then
    echo "Usage: $0 <RunNumber>"
    exit 1
fi
echo "Processing Run Number: $InputRunNumber"

if [ ! -d "$DatDataPath" ]; then
    echo "Data path does not exist: $DatDataPath"
    exit 1
fi

# check the data file exists
filename=$(get_run_file "$InputRunNumber")
if [ $? -ne 0 ]; then
    echo "Error: Could not find data file for RunNumber $InputRunNumber"
    exit 1
fi
echo "Found data file: $filename"

# Run the analysis script
echo "Running analysis script..."
PWD=$(pwd)
cd /eos/user/y/ymaruya/FASER/AHCAL-analyse/
mkdir -p run${InputRunNumber}
cd run${InputRunNumber}
TriggerLayer1=$2
TriggerLayer2=$3
if [ -z "$TriggerLayer1" ] || [ -z "$TriggerLayer2" ]; then
    echo "Usage: $0 <RunNumber> <TriggerLayer1> <TriggerLayer2>"
    exit 1
fi
# check the trigger layers are valid
if ! [[ "$TriggerLayer1" =~ ^([0-9]|[1-3][0-9])$ ]] || ! [[ "$TriggerLayer2" =~ ^([0-9]|[1-3][0-9])$ ]]; then
    echo "Error: Trigger layers must be integers between 0 and 39"
    exit 1
fi
../bin/ForMuon_eff_with_offset $filename ../calibration/pedestal.root ../calibration/dac.root ../calibration/mip.root muon_full.root $2 $3 MuonCandidate2.root Save
if [ $? -ne 0 ]; then
    echo "Error: Analysis script failed"
    exit 1
fi
echo "Analysis completed successfully."
cd "$PWD"





