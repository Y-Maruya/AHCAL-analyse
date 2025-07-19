#!/bin/bash

for runnumber in "$@"; do
    echo "Processing run number: $runnumber"
    ./auto.sh $runnumber
    ./auto_fT.sh $runnumber 4 14
done