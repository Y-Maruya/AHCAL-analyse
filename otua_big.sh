#!/bin/bash

for runnumber in "$@"; do
    echo "Processing run number: $runnumber"
    ./auto_big.sh $runnumber
done