# AHCAL Analysis

Analysis framework for the Analog Hadronic Calorimeter (AHCAL) data within the FASER experiment.

## Overview

This repository contains tools and scripts for analyzing data collected from the AHCAL detector.

## Installation

```bash
git clone https://github.com/username/AHCAL-analyse.git
cd AHCAL-analyse
cmake ./
make 
```

## Dependencies

- ROOT
- (HDF5 (not need for faser analysis, for converting the simulation data))

With lxplus.cern.ch, no need to load LCG.
You don't need to source something

## Usage
### For checking data and ploting HitMap and adc distribution (Test)
### For measuring the rate and select the muon candidates. (ForMuon_eff)
```bash
cd AHCAL-analyse
mkdir run*
cd run*
../bin/Test "The path of AHCAL data (.root)" ../calibration/pedestal.root ../calibration/dac.root ../calibration/mip.root test_run*.root
../bin/ForMuon_eff "The path of AHCAL data (.root)" ../calibration/pedestal.root ../calibration/dac.root ../calibration/mip.root muon_run*.root 14 34
```
(14 34 is the trigger layer)


### For converting and digitization
```bash
../bin/convert input.gfaser_calo.root output.h5
```