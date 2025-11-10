#ifndef Treew_h_
#define Treew_h_

// #include<TROOT.h>
//  #include<TChain.h>
#include <TFile.h>
#include <fstream>
#include <iostream>
#include <TCanvas.h>
#include <TH2.h>
#include <TTree.h>
using namespace std;
class raw2Root
{
private:
    static const int channel_FEE = 73; //(36charges+36times + BCIDs )*16column+ ChipID
    static const int cell_SP = 16;
    static const int chip_No = 9;
    static const int channel_No = 36;
    static const int Layer_No = 40;
    // const double _Pos_X[channel_No]={100.2411,100.2411,100.2411,59.94146,59.94146,59.94146,19.64182,19.64182,19.64182,19.64182,59.94146,100.2411,100.2411,59.94146,19.64182,100.2411,59.94146,19.64182,-20.65782,-60.95746,-101.2571,-20.65782,-60.95746,-101.2571,-101.2571,-60.95746,-20.65782,-20.65782,-20.65782,-20.65782,-60.95746,-60.95746,-60.95746,-101.2571,-101.2571,-101.2571};
    // const double _Pos_Y[channel_No]={141.04874,181.34838,221.64802,141.04874,181.34838,221.64802,141.04874,181.34838,221.64802,261.94766,261.94766,261.94766,302.2473,302.2473,302.2473,342.54694,342.54694,342.54694,342.54694,342.54694,342.54694,302.2473,302.2473,302.2473,261.94766,261.94766,261.94766,221.64802,181.34838,141.04874,221.64802,181.34838,141.04874,221.64802,181.34838,141.04874};
    // const double chip_dis_X=239.3;
    // const double chip_dis_Y=241.8;
    // const double HBU_X=239.3;
    // const double HBU_Y=725.4;
    int LayerNo;
    vector<int> chipNo;

public:
    int Decode(string binary_name, string raw_name);
    int BER(string binary_name);
    int RMFelixTag(string str_datalist, string outputDir);
    int CatchSPIROCBag(ifstream &f_in, vector<int> &buffer_v, int &layer_id, int &cycleID, int &triggerID);
    int FillChipBuffer(vector<int> &buffer_v, int cycleID, int triggerID, int layer_id);
    void SetTreeBranch(TTree *tree);
    void SetMIPTreeBranch(TTree *tree);
    void SetDataTree(TTree *tree);
    void ReadTreeBranch(TTree *tree);
    void ReadCalibTree(TTree *tree);
    void ReadMCTree(TTree *tree);
    int FillTreeBranch(TTree *tree, vector<int> &buffer_v, int cycleID, int triggerID, int layer_id);
    int DecodeAEvent(vector<int> &chip_v, int layer_ID, int Memo_ID);
    int AnaSPS(string str_in, string outputDir);
    int AnaPed(string str_in, string outputDir);
    int AnaCos(string str_in, string outputDir);
    int AnaBeam(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file);
    int EnergyCalib(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file);
    int Test(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file, int trigger_layer0, int trigger_layer1);
    int forMuon(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file);
    int forMuon_eff(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1);
    int forMuon_eff_mul(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file, string trigger_logic);
    // Muon efficiency analysis with residual calculation - calculates layer offsets
    int forMuon_eff_residual(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1);
    
    // Muon efficiency analysis with offset correction applied - uses pre-calculated offsets
    int forMuon_eff_with_offset(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1, double* x_offset, double* y_offset);
    int forMuon_eff_with_offset_trackSave(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1, double* x_offset, double* y_offset);
    int forMuon_eff_with_offset_perchip(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1, double* x_offset, double* y_offset);
    int forMuon_MC(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1, double* x_offset, double* y_offset);
    int Digitize(string str_dat, string str_ped, string str_dac, string str_MIP, string str_SPE, string str_lowgain_dac, string sipm_model, string output_file);
    int digi(double energy, double sipm_energy, double &HG, double &LG, int i);
    double digi_cal(double energy, double sipm_energy, double &HG, double &LG, int i);
    int neEnergyCalib(string str_dat, string str_MIP, string output_file, string mode);
    int nCorrect(string str_dat, string str_MIP, string str_SPE, string output_file);
    int MCDigi(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file);
    int EnergyRes(string str_list, string output_file, int Pri_E);
    int MuonCalib(string str_datalist, string str_ped, string output_file);
    int MuonSelect(string str_datalist, string str_ped, string output_file);
    int MuonFit(string input_file, string output_file);
    void Reset();
    void BranchClear();
    void CalibBranchClear();
    void deleteLocator();
    void triggerBuild(vector<int> bufferAsic);
    double cycleIDbuffer;
    int prevCycleID;
    int tluOverflow;
    int Chipbuffer_empty();
    int ReadList(const string _list);
    int MIPlist(const string _list);
    int PEDlist(const string _list,const string ishittag=0);
    int MIPlist(const string _list, string pedestal);
    int MIPlist2(const string _list);
    int MIP(vector<int> *_cellid, vector<double> *_HG_Charge);
    int MIP(vector<int> *_cellid, vector<int> *hitTag);
    int MIP(vector<int> *_cellid, vector<int> *hitTag, vector<double> *_HG_Charge, vector<int> *noise_cellid, vector<double> *noise_hit);
    
private:
    //    Event* EventClass;
    ifstream _f_in;
    int _Run_No = 0;
    unsigned int _Event_Time = 0;
    int _layer_id = 0;
    int _triggerID;
    int _Event_No;
    int _Detector_ID = 1;
    int _cycleID;
    double _Digi_Energy;
    double Digi_Energy;
    vector<int> _buffer_v;
    vector<int> _chip_v[Layer_No][chip_No];
    vector<int> _cellID;
    vector<int> _cherenkov;
    vector<double> _Hit_E;
    vector<double> _Hit_X;
    vector<double> _Hit_Y;
    vector<double> _Hit_Z;
    vector<double> _Hit_Time;
    vector<double> _time;
    vector<int> *cellID = 0;
    vector<int> *data_cellid = 0;
    vector<int> *bcid = 0;
    vector<int> *hitTag = 0;
    vector<int> *gainTag = 0;
    vector<int> *cherenkov = 0;
    vector<double> *HG_Charge = 0;
    vector<double> *LG_Charge = 0;
    vector<double> *Hit_Time = 0;
    vector<double> *Hit_E=0;
    vector<double> *Hit_X=0;
    vector<double> *Hit_Y=0;
    vector<double> *Hit_Z=0;
    vector<double> *SiPM_Energy=0;
    vector<double> *SiPM_Hit=0;
    vector<double> _temp;
    vector<string> list;
};
#endif
