#!/bin/bash
InputRunNumber=$1
# DatDataPath="/eos/user/s/shunlian/AHCAL/data/stable_test/"
DatDataPath="/afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-data-EHN1/"
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
cd /eos/user/y/ymaruya/FASER/AHCAL-analyse-EHN1/
mkdir -p run${InputRunNumber}_calibed_perchip_trigger037
cd run${InputRunNumber}_calibed_perchip_trigger037
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
# /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/bin/ForMuon_eff $filename /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/pedestal.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/dac.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/mip.root muon_full.root $2 $3
# /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/bin/ForMuon_eff_ADC $filename /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/pedestal.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/dac.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/mip.root muon_full.root $2 $3 
/afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/bin/ForMuon_eff_ADC_MIPcalibed_perchip $filename /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/pedestal.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/dac.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse-EHN1/run32/MuonADC_offset.root_mip.root muon_full.root $2 $3 

# /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/bin/Test $filename /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/pedestal.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/dac.root /afs/cern.ch/user/y/ymaruya/private/FASERlink/AHCAL-analyse/calibration/mip.root test.root $2 $3
if [ $? -ne 0 ]; then
    echo "Error: Analysis script failed"
    cd $PWD
else
    echo "Analysis completed successfully."
    cd $PWD
fi



