#include <iostream>
#include <vector>
#include <string>
#include <H5Cpp.h>
#include <TFile.h>
#include <TTree.h>
#include <TF1.h>
#include <TRandom.h>
#include <TEventList.h>
#include <TBranch.h>
#include "RawtoRoot.h"
#include "Global.h"
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <algorithm>
#include <time.h>
#include <stdlib.h>
#include <TFile.h>
#include <TTree.h>
#include <vector>
#include <TROOT.h>
#include <TSystem.h>
#include <TMath.h>
#include <string>
#include <TF1.h>
#include <TH1.h>
#include <TStyle.h>
#include "TMath.h"
#include "TRandom3.h"
#include <TSpectrum.h>
#include "TLegend.h"
#include "TLine.h"
#include "TVirtualFitter.h"
#include "TGraphErrors.h"
#include "TGraph.h"
#include "TGaxis.h"

int layer, chip, channel;
using namespace std;
char char_tmp[200];
double ped_high[Layer_No][chip_No][channel_No];
double ped_low[Layer_No][chip_No][channel_No];
double rms_high[Layer_No][chip_No][channel_No];
double rms_low[Layer_No][chip_No][channel_No];
double gain_ratio[Layer_No][chip_No][channel_No];
double gain_plat[Layer_No][chip_No][channel_No];
double lowgain_plat[Layer_No][chip_No][channel_No];
double _MIP[Layer_No][chip_No][channel_No];
double SPE[Layer_No][chip_No][channel_No];
double chi2_ndf[Layer_No][chip_No][channel_No];
double NDF[Layer_No][chip_No][channel_No];
double Sigma[Layer_No][chip_No][channel_No];
double lp[Layer_No][chip_No][channel_No][2];
double p[Layer_No][chip_No][channel_No][5];
double lowgain_max[Layer_No][chip_No][channel_No];
TH1I *h_sipm[15000];
double MIP_E = 0.461; // MeV
int pixel = 7284;
double pde = 0.32;
TF1* fun5=new TF1("fun5","x-8.57e-5*x^2+2.108e-9*x^3",0,50000);
TF1* fun6=new TF1("fun6","x-1.0e-5*x^2-1.868e-8*x^3+1.355e-12*x^4",0,50000);
TF1* funline=new TF1("funline","[0]+[1]*x",0,10000);
TF1* funall=new TF1("funall","[0]+[1]*x+[2]*x^2+[3]*x^3+[4]*x^4",0,10000);
double par[5]={393.877,0.138625,4.03238e-06,-1.09848e-09,4.31359e-14};
// fun5->SetParameters(-8.249e-5,1.329e-9);
// fun6->SetParameters(1.368e-5,-2.825e-8,2.261e-12);

int raw2Root::Digitize(string str_dat, string str_ped, string str_dac, string str_MIP, string str_SPE, string str_lowgain_dac, string sipm_model, string output_file)
{
    string str_out = output_file;
    TFile *fin, *fout;
    TTree *tree_in, *tree_out;
    double hitE, hitE_layer[Layer_No], hitNo_layer[Layer_No];
    double Edep = 0;
    double SwitchPoint = 500;
    const double ref_ped_high = 374;
    const double ref_rms_high = 3.5;
    const double ref_ped_low = 371;
    const double ref_rms_low = 2.3;
    const double ref_MIP = 344.3;
    const double ref_gain_ratio = 26;
    const double ref_gain_plat = 2927;
    const double ref_spe = 27.7;
    const double ref_sigma = 7;
    int Select_EventNo = 0;
    int HitNo = 0;
    int CellID = 0;
    double MPV = 0;
    int Tag = 0;
    float slope = 0;
    float plat = 0;
    float low_plat = 0;
    double pedestal_high = 0, sigma_high = 0;
    double pedestal_low = 0, sigma_low = 0;
    double spe = 0, sigma = 0, chi2 = 0, ndf = 0;
    double lp0 = 0, lp1 = 0, p0 = 0, p1 = 0, p2 = 0, p3 = 0, p4 = 0;
    double _max = 0;
    double Layer_E[Layer_No] = {0};
    TH1D *h_Edep;
    TH2D *h2_HitE_Layer;
    TH2D *h2_HitMap;
    sprintf(char_tmp, "Energy deposition");
    // h_Edep = new TH1D(char_tmp,char_tmp,1000,0,3);
    // h2_HitE_Layer = new TH2D(char_tmp,char_tmp,100,0,100,40,0,40);
    sprintf(char_tmp, "Hit Map");
    h2_HitMap = new TH2D(char_tmp, char_tmp, 18, -360, 360, 18, -360., 360.);
    // read ped
    fin = TFile::Open(str_ped.c_str(), "READ");
    if (!fin)
    {
        cout << "cant open " << str_ped << endl;
        return 0;
    }
    tree_in = (TTree *)fin->Get("pedestal");
    if (!tree_in)
    {
        cout << "cant get tree pedestal" << endl;
        return 0;
    }
    tree_in->SetBranchAddress("cellid", &CellID);
    tree_in->SetBranchAddress("highgain_peak", &pedestal_high);
    tree_in->SetBranchAddress("lowgain_peak", &pedestal_low);
    tree_in->SetBranchAddress("highgain_rms", &sigma_high);
    tree_in->SetBranchAddress("lowgain_rms", &sigma_low);
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer)
    {
        for (int i_chip = 0; i_chip < chip_No; ++i_chip)
        {
            for (int i_chan = 0; i_chan < channel_No; ++i_chan)
            {
                ped_high[i_layer][i_chip][i_chan] = -1;
                ped_low[i_layer][i_chip][i_chan] = -1;
                rms_high[i_layer][i_chip][i_chan] = -1;
                rms_low[i_layer][i_chip][i_chan] = -1;
                _MIP[i_layer][i_chip][i_chan] = -1;
                gain_ratio[i_layer][i_chip][i_chan] = -1;
                SPE[i_layer][i_chip][i_chan] = -1;
                Sigma[i_layer][i_chip][i_chan] = -1;
            }
        }
    }
    for (int i = 0; i < tree_in->GetEntries(); ++i)
    {
        tree_in->GetEntry(i);
        decode_cellid(CellID, layer, chip, channel);
        // cout<<layer<<" "<<chip<<" "<<channel<<" "<<pedestal_time<<" "<<pedestal_charge<<endl;
        ped_high[layer][chip][channel] = pedestal_high;
        rms_high[layer][chip][channel] = sigma_high;
        ped_low[layer][chip][channel] = pedestal_low;
        rms_low[layer][chip][channel] = sigma_low;
    }
    tree_in->Delete();
    fin->Close();
    // read dac
    fin = TFile::Open(str_dac.c_str(), "READ");
    if (!fin)
    {
        cout << "cant open " << str_dac << endl;
        return 0;
    }
    // tree_in = (TTree*)fin->Get("calib");
    tree_in = (TTree *)fin->Get("dac");
    if (!tree_in)
    {
        cout << "cant get tree dac" << endl;
        return 0;
    }
    tree_in->SetBranchAddress("cellid", &CellID);
    tree_in->SetBranchAddress("slope", &slope);
    tree_in->SetBranchAddress("plat", &plat);
    tree_in->SetBranchAddress("lowgain_satu_point", &low_plat);
    for (int i = 0; i < tree_in->GetEntries(); ++i)
    {
        tree_in->GetEntry(i);
        decode_cellid(CellID, layer, chip, channel);
        // cout<<layer<<" "<<chip<<" "<<channel<<" "<<slope<<" "<<endl;
        gain_ratio[layer][chip][channel] = slope;
        gain_plat[layer][chip][channel] = plat;
        lowgain_plat[layer][chip][channel] = low_plat;
        if (gain_ratio[layer][chip][channel] < 10 || gain_ratio[layer][chip][channel] > 50)
            cout << CellID << " abnormal gain ratio " << layer << " " << chip << " " << channel << " " << slope << endl;
    }
    tree_in->Delete();
    fin->Close();
    // read MIP
    fin = TFile::Open(str_MIP.c_str(), "READ");
    if (!fin)
    {
        cout << "cant open " << str_MIP << endl;
        return 0;
    }
    tree_in = (TTree *)fin->Get("MIP_Calibration");
    if (!tree_in)
    {
        cout << "cant get MIP tree" << endl;
        return 0;
    }
    tree_in->SetBranchAddress("CellID", &CellID);
    tree_in->SetBranchAddress("MPV", &MPV);
    tree_in->SetBranchAddress("Tag", &Tag);
    // tree_in->SetBranchAddress("ID",&CellID);
    // tree_in->SetBranchAddress("mpv",&MPV);
    for (int i = 0; i < tree_in->GetEntries(); ++i)
    {
        tree_in->GetEntry(i);
        decode_cellid(CellID, layer, chip, channel);
        // MIP[layer][chip][channel]=MPV - ped_time[layer][chip][channel];
        _MIP[layer][chip][channel] = MPV;
        if (Tag != 1)
            _MIP[layer][chip][channel] = ref_MIP;
        // cout<<layer<<" "<<chip<<" "<<channel<<" "<<MPV<<endl;
        //  if(_MIP[layer][chip][channel]<200)cout<<"abnormal MIP "<<layer<<" "<<chip<<" "<<channel<<" "<<MPV<<endl;
    }
    tree_in->Delete();
    fin->Close();
    // read SPE
    fin = TFile::Open(str_SPE.c_str(), "READ");
    if (!fin)
    {
        cout << "cant open " << str_MIP << endl;
        return 0;
    }
    tree_in = (TTree *)fin->Get("spe");
    if (!tree_in)
    {
        cout << "cant get sipm gain tree" << endl;
        return 0;
    }
    tree_in->SetBranchAddress("cellid", &CellID);
    tree_in->SetBranchAddress("spe", &spe);
    tree_in->SetBranchAddress("sigma", &sigma);
    tree_in->SetBranchAddress("chi2", &chi2);
    tree_in->SetBranchAddress("ndf", &ndf);
    for (int i = 0; i < tree_in->GetEntries(); ++i)
    {
        tree_in->GetEntry(i);
        decode_cellid(CellID, layer, chip, channel);
        SPE[layer][chip][channel] = spe;
        chi2_ndf[layer][chip][channel] = chi2 / ndf;
        NDF[layer][chip][channel] = ndf;
        Sigma[layer][chip][channel] = sigma;
    }
    tree_in->Delete();
    fin->Close();
    // read lowgain dac
    // cout << "reading lowgain dac" << endl;
    // fin = TFile::Open(str_lowgain_dac.c_str(), "READ");
    // if (!fin)
    // {
    //     cout << "cant open " << str_lowgain_dac << endl;
    //     return 0;
    // }
    // tree_in = (TTree *)fin->Get("lowgain dac");
    // if (!tree_in)
    // {
    //     cout << "cant get lowgain dac tree" << endl;
    //     return 0;
    // }
    // tree_in->SetBranchAddress("cellid", &CellID);
    // tree_in->SetBranchAddress("lp0", &lp0);
    // tree_in->SetBranchAddress("lp1", &lp1);
    // tree_in->SetBranchAddress("p0", &p0);
    // tree_in->SetBranchAddress("p1", &p1);
    // tree_in->SetBranchAddress("p2", &p2);
    // tree_in->SetBranchAddress("p3", &p3);
    // tree_in->SetBranchAddress("p4", &p4);
    // cout << "open done" << endl;
    // for (int i = 0; i < tree_in->GetEntries(); ++i)
    // {
    //     tree_in->GetEntry(i);
    //     decode_cellid(CellID, layer, chip, channel);
    //     lp[layer][chip][channel][0] = lp0;
    //     lp[layer][chip][channel][1] = lp1;
    //     // cout << CellID<<"  "<<layer << "  " << chip << "  " << channel << "  " << lp0 << "  " << lp1 << endl;
    //     p[layer][chip][channel][0] = p0;
    //     p[layer][chip][channel][1] = p1;
    //     p[layer][chip][channel][2] = p2;
    //     p[layer][chip][channel][3] = p3;
    //     p[layer][chip][channel][4] = p4;
    //     lowgain_max[layer][chip][channel] = _max;
    // }
    // cout << "open done" << endl;
    // delete tree_in;
    // cout << "delete done" << endl;
    // // fin->Close();
    // cout << "reading lowgain dac done" << endl;
    // smooth parameters
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer)
    {
        for (int i_chip = 0; i_chip < chip_No; ++i_chip)
        {
            double mean_gain = 0;
            int n_good = 0;
            for (int i_chan = 0; i_chan < channel_No; ++i_chan)
            {
                if (ped_high[i_layer][i_chip][i_chan] < 0)
                    ped_high[i_layer][i_chip][i_chan] = ref_ped_high;
                if (rms_high[i_layer][i_chip][i_chan] < 0)
                    rms_high[i_layer][i_chip][i_chan] = ref_rms_high;
                if (ped_low[i_layer][i_chip][i_chan] < 0)
                    ped_low[i_layer][i_chip][i_chan] = ref_ped_low;
                if (rms_low[i_layer][i_chip][i_chan] < 0)
                    rms_low[i_layer][i_chip][i_chan] = ref_rms_high;
                if (_MIP[i_layer][i_chip][i_chan] < 100)
                    _MIP[i_layer][i_chip][i_chan] = ref_MIP;
                if (gain_ratio[i_layer][i_chip][i_chan] < 0)
                    gain_ratio[i_layer][i_chip][i_chan] = ref_gain_ratio;
                if (lowgain_plat[i_layer][i_chip][i_chan] < 2000)
                    lowgain_plat[i_layer][i_chip][i_chan] = 2000;
                if (gain_plat[i_layer][i_chip][i_chan] < 0)
                    gain_plat[i_layer][i_chip][i_chan] = ref_gain_plat;
                if (Sigma[i_layer][i_chip][i_chan] < 0)
                    Sigma[i_layer][i_chip][i_chan] = ref_sigma;
                if (chi2_ndf[layer][chip][channel] < 20 || NDF[layer][chip][channel] <= 3 || SPE[layer][chip][channel] < 15)
                {
                    mean_gain += SPE[layer][chip][channel];
                    n_good++;
                }
            }
            mean_gain /= n_good;
            for (int i_chan = 0; i_chan < channel_No; ++i_chan)
            {
                if (chi2_ndf[layer][chip][channel] >= 20 || SPE[layer][chip][channel] < mean_gain - 5 || SPE[layer][chip][channel] > mean_gain + 5 || NDF[layer][chip][channel] <= 3 || SPE[layer][chip][channel] < 15)
                {
                    SPE[layer][chip][channel] = mean_gain;
                }
            }
        }
    }
    // read sipm model histogram
    fin = TFile::Open(sipm_model.c_str(), "READ");
    for (int i = 0; i < 15000; i++)
    {
        TString name = "hist/incident_" + TString(std::to_string(i + 1).c_str()) + "_photons";
        h_sipm[i] = (TH1I *)fin->Get(name);
    }
    // fin->Close();
    // read sipm model histogram done
    // read dat
    // TFile *fin1 = TFile::Open(str_dat.c_str(), "READ");
    // if (!fin1)
    // {
    //     cout << "cant open " << str_dat << endl;
    //     return 0;
    // }
    // cout << "Read TTree " << endl;
    // tree_in = (TTree *)fin1->Get("EventTree");
    // ReadMCTree(tree_in);
    // cout << "Read TTree Over" << endl;
    // fout = TFile::Open(str_out.c_str(), "RECREATE");
    // if (!fout)
    // {
    //     cout << "cant open " << str_out << endl;
    //     return 0;
    // }
    // cout << "digitizing " << str_dat << endl;
    // tree_out = new TTree("Raw_Hit", "Hits afer digitization");
    // SetDataTree(tree_out);
    gRandom = new TRandom3(0);
    funall->SetParameters(par);
    // for (int i = 0; i < tree_in->GetEntries(); ++i)
    // {
    //     BranchClear();
    //     if ((i % 10000) == 0)
    //         cout << i << " out of " << tree_in->GetEntries() << endl;
    //     // if(i>39000)cout<<i<<endl;
    //     tree_in->GetEntry(i);
    //     for (int i_hit = 0; i_hit < cellID->size(); i_hit++)
    //     {
    //         hitTag->push_back(1);
    //         int cid = cellID->at(i_hit);
    //         // cout<<cid<<" "<<layer<<" "<<chip<<" "<<channel<<endl;
    //         data_cellid->push_back(cid);
    //         double HG = 0, LG = 0;
    //         digi(Hit_E->at(i_hit) , 0, HG, LG, cid);
    //         HG_Charge->push_back(HG);
    //         LG_Charge->push_back(LG);
    //         // h2_HitMap->Fill(Hit_X->at(i_hit)/40.3,Hit_Y->at(i_hit)/40.3);
    //         // Hit_Time->push
    //     }
    //     tree_out->Fill();
    // }
    // fout->cd();
    // tree_out->Write();
    // // h2_HitMap->Write();
    // // h_Edep->Write();
    // fout->Close();
    // cout << "digitization done" << endl;
    // cout << endl;
    return 1;
}
double raw2Root::digi(double energy, double sipm_energy, double &HG, double &LG, int cid)
{
    decode_cellid(cid, layer, chip, channel);
    // energy += sipm_energy / 10 * 1e6 / 3.6 / _MIP[layer][chip][channel] * SPE[layer][chip][channel] * MIP_E;
    // nonuniform of Scintillators
    energy = gRandom->Gaus(energy, energy * 0.048);
    // energy = gRandom->Gaus(energy, energy * 0.048);
    // energy to photon
    if(energy<=0)
        energy = 0;
    double n_photon = energy / MIP_E * _MIP[layer][chip][channel] / SPE[layer][chip][channel] / pde;
    n_photon = gRandom->Poisson(n_photon);
    // photon to photoelectron
    int n_photoelectron = gRandom->Binomial(int(n_photon), pde);
    ///////////////////////////////////////////
    // SiPM model                            //
    // int n_fired=0;                        //
    // bool isa[pixel];                      //
    // std::fill(isa,isa+pixel,0);           //
    // for(int n=0;n<n_photoelectron;n++){   //
    //     int npx=gRandom->Integer(pixel);  //
    //     if(isa[npx])continue;             //
    //     isa[npx]=1;                       //
    //     n_fired++;                        //
    // }                                     //
    ///////////////////////////////////////////
    if (n_photoelectron >= 15000)
    {
        cout << n_photoelectron << endl;
        n_photoelectron = 14999;
    }
    int n_fired;
    if (n_photoelectron == 0)
    {
        n_fired = 0;
    }
    else{
        n_fired = int(h_sipm[n_photoelectron-1]->GetRandom());
    }
    // if(n_fired>n_photoelectron)
    //     cout << n_fired << "  " << n_photoelectron << endl;
    // int n_fired = n_photoelectron;
    ////////////////////////////////////////////////////////////////////////////////////////
    // double n_fired_mean=pixel * (1.0 - TMath::Exp(-n_photoelectron * 1.0 / pixel));    //
    // double n_fired_sigma=32.62 * (1.0 - TMath::Exp(-n_photoelectron / 3847));          //
    // int n_fired = round(gRandom->Gaus(n_fired_mean , n_fired_sigma));                  //
    ////////////////////////////////////////////////////////////////////////////////////////
    // spe error
    double adc = n_fired * SPE[layer][chip][channel];
    double adc_sigma = sqrt(n_fired) * 10; // Sigma[layer][chip][channel];
    // TODO
    adc = gRandom->Gaus(adc, adc_sigma);
    // ADC to HG LG
    HG = adc + gRandom->Gaus(ped_high[layer][chip][channel], 1.5*rms_high[layer][chip][channel]);
    // HG = adc + gRandom->Gaus(ped_high[layer][chip][channel], 20);
    LG = adc / gain_ratio[layer][chip][channel] + gRandom->Gaus(ped_low[layer][chip][channel], 5*rms_low[layer][chip][channel]);
    if (HG > gain_plat[layer][chip][channel])
    {
        HG = gain_plat[layer][chip][channel];
    }
    // if(int(cid/1e5)==6){
    //     // cout<<"old: "<<LG<<endl;
    //     LG=fun6->Eval(LG-ped_low[layer][chip][channel])+ped_low[layer][chip][channel];
    //     // cout<<"new: "<<LG<<endl;
    //     // cout<<"\n";
    // }
    // else if(int(cid/1e5)==5){
    //     // cout<<"old: "<<LG<<endl;
    //     LG=fun5->Eval(LG-ped_low[layer][chip][channel])+ped_low[layer][chip][channel];
    //     // cout<<"new: "<<LG<<endl;
    //     // cout<<"\n";
    // }
    if (LG > lowgain_plat[layer][chip][channel])
    {
        LG = lowgain_plat[layer][chip][channel];
    }
    // cout << LG << "   ";
    // funline->SetParameter(0, -lp[layer][chip][channel][0] / lp[layer][chip][channel][1]);
    // funline->SetParameter(1, 1/lp[layer][chip][channel][1]);
    // funall->SetParameters(p[layer][chip][channel]);
    // double dac = funline->Eval(LG);
    // // cout << dac <<"  "<<layer<<"  "<<chip<<"  " <<channel<<"  "<<lp[layer][chip][channel][0] << "  " << lp[layer][chip][channel][1] << "   ";
    // double shift = (ped_low[layer][chip][channel] - lp[layer][chip][channel][0]) / lp[layer][chip][channel][1];
    // if (dac > 4000)
    //     dac = 4000;
    // if(dac>2000)
    // {
    //     LG = funall->Eval(dac);
    //     // if (LG > 800)
    //     // {
    //     //     LG = 800;
    //     // }
    // }
    // // cout << LG << endl;
    // HG = round(HG);
    // LG = round(LG);
    // cout<<energy<<"  "<<n_fired<<"  "<<HG<<endl;
    double hitE = 0;
    double SwitchPoint=500;
    if( (HG)-ped_high[layer][chip][channel] < gain_plat[layer][chip][channel]-SwitchPoint )
    {
        hitE=( HG- ped_high[layer][chip][channel] )*MIP_E/_MIP[layer][chip][channel];
    }
    else
    {
        hitE=( LG- ped_low[layer][chip][channel] )*MIP_E/_MIP[layer][chip][channel];
    }
    return hitE;
}

using namespace H5;
Int_t GetBin1d(int bin1,int bin2,int bin3){
    return (bin1)*42+(bin2)+(bin3)*42*5;
}
Int_t GetBin1d_AHCAL(int bin1,int bin2,int bin3){
   return (bin1)*18+(bin2)+(bin3)*18*18;
}

void convert_caloroot_to_h5(const std::string& root_file_path, const std::string& tree_name, const std::string& h5_file_path, size_t batch_size = 1000) {
    // Open the ROOT file
    TFile* root_file = TFile::Open(root_file_path.c_str());
    if (!root_file || root_file->IsZombie()) {
        std::cerr << "Error opening ROOT file: " << root_file_path << std::endl;
        return;
    }

    // Get the tree from the ROOT file
    TTree* tree = (TTree*)root_file->Get(tree_name.c_str());
    if (!tree) {
        std::cerr << "Error getting tree: " << tree_name << " from ROOT file: " << root_file_path << std::endl;
        root_file->Close();
        return;
    }
    tree->Draw(">>elist", "ftagNulabel<4");
    TEventList *elist = (TEventList*)gDirectory->Get("elist");
    tree->SetEventList(elist);
    SiPMResponseFit->SetParameters(3082.88, 1.35524, 4.0577, 0.0206382, 0.109543);
    std::cout << "Number of entries in the tree: " << elist->GetN() << std::endl;
    // Variables to hold the data
    // int ftagNulabel;
    // double Interaction_x, Interaction_y, Interaction_z;
    // double energy_deposit_SciW[16*42*5*2];
    // double energy_deposit_AHCAL[18*18*40];

    // Set branch addresses
    Int_t EvtID;
    Double_t ParticleEnergy;
    Double_t Interaction_x;
    Double_t Interaction_y;
    Double_t Interaction_z;
    Int_t ftagNulabel;
    // Double_t CaloEdepSum;
    // Double_t CaloVisibleEdepSum;
    // Double_t EcalEdepSum;
    // Double_t EcalVisibleEdepSum;
    // Double_t HcalEdepSum;
    // Double_t HcalVisibleEdepSum;
    // Double_t EcalMaxEdepCell;
    // Double_t HcalMaxEdepCell;
    std::vector<Int_t>* vecEcalCellID = nullptr;
    // std::vector<Int_t>* vecEcalStepsCell = nullptr;
    // std::vector<Double_t>* vecEcalEdepCell = nullptr;
    std::vector<Double_t>* vecEcalVisibleEdepCell = nullptr;
    // std::vector<Double_t>* vecEcalHitTimeCell = nullptr;
    // std::vector<Double_t>* vecEcalToaCell = nullptr;
    std::vector<Int_t>* vecHcalCellID = nullptr;
    // std::vector<Int_t>* vecHcalStepsCell = nullptr;
    // std::vector<Double_t>* vecHcalEdepCell = nullptr;
    std::vector<Double_t>* vecHcalVisibleEdepCell = nullptr;
    // std::vector<Double_t>* vecHcalHitTimeCell = nullptr;
    // std::vector<Double_t>* vecHcalToaCell = nullptr;
    tree->SetBranchStatus("*", 0);
    tree->SetBranchStatus("EvtID", 1);
    tree->SetBranchStatus("ParticleEnergy", 1);
    tree->SetBranchStatus("Interaction_x", 1);
    tree->SetBranchStatus("Interaction_y", 1);
    tree->SetBranchStatus("Interaction_z", 1);
    tree->SetBranchStatus("ftagNulabel", 1);
    // tree->SetBranchStatus("CaloEdepSum", 1);
    // tree->SetBranchStatus("CaloVisibleEdepSum", 1);
    // tree->SetBranchStatus("EcalEdepSum", 1);
    // tree->SetBranchStatus("EcalVisibleEdepSum", 1);
    // tree->SetBranchStatus("HcalEdepSum", 1);
    // tree->SetBranchStatus("HcalVisibleEdepSum", 1);
    // tree->SetBranchStatus("EcalMaxEdepCell", 1);
    // tree->SetBranchStatus("HcalMaxEdepCell", 1);
    tree->SetBranchStatus("vecEcalCellID", 1);
    // tree->SetBranchStatus("vecEcalStepsCell", 1);
    // tree->SetBranchStatus("vecEcalEdepCell", 1);
    tree->SetBranchStatus("vecEcalVisibleEdepCell", 1);
    // tree->SetBranchStatus("vecEcalHitTimeCell", 1);
    // tree->SetBranchStatus("vecEcalToaCell", 1);
    tree->SetBranchStatus("vecHcalCellID", 1);
    // tree->SetBranchStatus("vecHcalStepsCell", 1);
    // tree->SetBranchStatus("vecHcalEdepCell", 1);
    tree->SetBranchStatus("vecHcalVisibleEdepCell", 1);
    // tree->SetBranchStatus("vecHcalHitTimeCell", 1);
    // tree->SetBranchStatus("vecHcalToaCell", 1);
    tree->SetBranchAddress("EvtID", &EvtID);
    tree->SetBranchAddress("ParticleEnergy", &ParticleEnergy);
    tree->SetBranchAddress("Interaction_x", &Interaction_x);
    tree->SetBranchAddress("Interaction_y", &Interaction_y);
    tree->SetBranchAddress("Interaction_z", &Interaction_z);
    tree->SetBranchAddress("ftagNulabel", &ftagNulabel);
    // tree->SetBranchAddress("CaloEdepSum", &CaloEdepSum);
    // tree->SetBranchAddress("CaloVisibleEdepSum", &CaloVisibleEdepSum);
    // tree->SetBranchAddress("EcalEdepSum", &EcalEdepSum);
    // tree->SetBranchAddress("EcalVisibleEdepSum", &EcalVisibleEdepSum);
    // tree->SetBranchAddress("HcalEdepSum", &HcalEdepSum);
    // tree->SetBranchAddress("HcalVisibleEdepSum", &HcalVisibleEdepSum);
    // tree->SetBranchAddress("EcalMaxEdepCell", &EcalMaxEdepCell);
    // tree->SetBranchAddress("HcalMaxEdepCell", &HcalMaxEdepCell);
    tree->SetBranchAddress("vecEcalCellID", &vecEcalCellID);
    // tree->SetBranchAddress("vecEcalStepsCell", &vecEcalStepsCell);
    // tree->SetBranchAddress("vecEcalEdepCell", &vecEcalEdepCell);
    tree->SetBranchAddress("vecEcalVisibleEdepCell", &vecEcalVisibleEdepCell);
    // tree->SetBranchAddress("vecEcalHitTimeCell", &vecEcalHitTimeCell);
    // tree->SetBranchAddress("vecEcalToaCell", &vecEcalToaCell);
    tree->SetBranchAddress("vecHcalCellID", &vecHcalCellID);
    // tree->SetBranchAddress("vecHcalStepsCell", &vecHcalStepsCell);
    // tree->SetBranchAddress("vecHcalEdepCell", &vecHcalEdepCell);
    tree->SetBranchAddress("vecHcalVisibleEdepCell", &vecHcalVisibleEdepCell);
    // tree->SetBranchAddress("vecHcalHitTimeCell", &vecHcalHitTimeCell);
    // tree->SetBranchAddress("vecHcalToaCell", &vecHcalToaCell);
    
    // Create the HDF5 file
    H5File h5_file(h5_file_path, H5F_ACC_TRUNC);

    // Create datasets in the HDF5 file
    hsize_t total_entries = static_cast<hsize_t>(elist->GetN());
    // hsize_t total_entries = 100;
    hsize_t dims[1] = { total_entries };
    DataSpace dataspace(1, dims);

    DataSet dataset_ftagNulabel = h5_file.createDataSet("ftagNulabel", PredType::NATIVE_INT, dataspace);
    DataSet dataset_ParticleEnergy = h5_file.createDataSet("ParticleEnergy", PredType::NATIVE_FLOAT, dataspace);
    DataSet dataset_Interaction_x = h5_file.createDataSet("Interaction_x", PredType::NATIVE_FLOAT, dataspace);
    DataSet dataset_Interaction_y = h5_file.createDataSet("Interaction_y", PredType::NATIVE_FLOAT, dataspace);
    DataSet dataset_Interaction_z = h5_file.createDataSet("Interaction_z", PredType::NATIVE_FLOAT, dataspace);
    DataSet dataset_total_energy_SciW = h5_file.createDataSet("total_energy_SciW", PredType::NATIVE_FLOAT, dataspace);
    DataSet dataset_total_energy_AHCAL = h5_file.createDataSet("total_energy_AHCAL", PredType::NATIVE_FLOAT, dataspace);
    // Define the shape for SciW and AHCAL data
    hsize_t dims_SciW[4] = { total_entries, 32, 5, 42 };
    hsize_t dims_AHCAL[4] = { total_entries, 40, 18, 18 };
    DataSpace dataspace_SciW(4, dims_SciW);
    DataSpace dataspace_AHCAL(4, dims_AHCAL);

    DataSet dataset_energy_deposit_SciW = h5_file.createDataSet("energy_deposit_SciW", PredType::NATIVE_FLOAT, dataspace_SciW);
    DataSet dataset_energy_deposit_AHCAL = h5_file.createDataSet("energy_deposit_AHCAL", PredType::NATIVE_FLOAT, dataspace_AHCAL);

    // Buffers to hold the data
    std::vector<int> ftagNulabel_data(batch_size);
    std::vector<float> ParticleEnergy_data(batch_size);
    std::vector<float> Interaction_x_data(batch_size);
    std::vector<float> Interaction_y_data(batch_size);
    std::vector<float> Interaction_z_data(batch_size);
    std::vector<float> total_energy_SciW_data(batch_size);
    std::vector<float> total_energy_AHCAL_data(batch_size);
    std::vector<float> energy_deposit_SciW_data(batch_size * 32 * 42 * 5);
    std::vector<float> energy_deposit_AHCAL_data(batch_size * 40 * 18 * 18);

    raw2Root tw;
    tw.Digitize("","../calibration/pedestal.root","../calibration/dac_v2.root","../calibration/mip.root","../calibration/spe.root","","../calibration/sipm_model/sipm_model_0.0xt.root","");
    // Loop over the entries in the tree in batches
    for (Long64_t start = 0; start < total_entries; start += batch_size) {
        Long64_t end = std::min(start + batch_size, total_entries);
        Long64_t current_batch_size = end - start;

        for (Long64_t i = start; i < end; ++i) {
            if (tree->GetEntry(elist->GetEntry(i)) <= 0) {
                std::cerr << "Error reading entry: " << i << std::endl;
                continue;
            }
            size_t index = i - start;
            ftagNulabel_data[index] = ftagNulabel;
            ParticleEnergy_data[index] = ParticleEnergy;
            Interaction_x_data[index] = Interaction_x;
            Interaction_y_data[index] = Interaction_y;
            Interaction_z_data[index] = Interaction_z;
            total_energy_SciW_data[index] = 0;
            total_energy_AHCAL_data[index] = 0;
            for(int i=0;i<32*42*5;i++){
                energy_deposit_SciW_data[index*32*42*5+i]=0;
            }
            for(int i=0;i<40*18*18;i++){
                energy_deposit_AHCAL_data[index*40*18*18+i]=0;
            }
            for (auto it = vecEcalCellID->begin(); it != vecEcalCellID->end(); it++)
            {
                Int_t ID_X = *it % 100;
                Int_t ID_Y = *it % 10000 / 100;
                Int_t ID_Z = *it / 10000;
                if (ID_Z % 2 == 0)
                    std::swap(ID_X, ID_Y);
                double tmp_energy=vecEcalVisibleEdepCell->at(std::distance(vecEcalCellID->begin(), it));
                Int_t ChipID = (ID_Y - 1) / 7;
                Int_t MemoID = 0;
                Int_t ChannelID = (ID_Y - 1) % 7 * 5 + (ID_X - 1);
                Int_t CellID = (ID_Z - 1) * 1e5 + ChipID * 1e4 + MemoID * 1e2 + ChannelID;
                // double tmp_energy_digi=SiPMDigi(tmp_energy,(CellID/100000 - 40) / 38, 1);
                double tmp_energy_digi=tmp_energy;
                if(energy_deposit_SciW_data[index*32*42*5+GetBin1d(ID_X-1,ID_Y-1,ID_Z-1)]>0){
                    std::cout<<"Error: energy deposit already exists"<<std::endl;
                }else{
                    energy_deposit_SciW_data[index*32*42*5+GetBin1d(ID_X-1,ID_Y-1,ID_Z-1)]=tmp_energy_digi;
                }
                total_energy_SciW_data[index]+=tmp_energy_digi;
            }
            for (auto it = vecHcalCellID->begin(); it != vecHcalCellID->end(); it++)
            {
                Int_t ID_X = *it % 100;
                Int_t ID_Y = *it % 10000 / 100;
                Int_t ID_Z = *it / 10000;
                Int_t ChipID = (ID_X - 1) / 6 + (ID_Y - 1) / 6 * 3;
                Int_t MemoID = 0;
                Int_t ChannelID = (ID_X - 1) % 6 + (ID_Y - 1) % 6 * 6;
                Int_t CellID = (ID_Z - 1) * 1e5 + ChipID * 1e4 + MemoID * 1e2 + ChannelID;
                double tmp_energy=vecHcalVisibleEdepCell->at(std::distance(vecHcalCellID->begin(), it));
                double HG = 0, LG = 0;
                double tmp_energy_digi = digi(tmp_energy, 0, HG, LG, CellID);
                if(energy_deposit_AHCAL_data[index*40*18*18+GetBin1d_AHCAL(ID_X-1,ID_Y-1,ID_Z-1)]>0){
                    std::cout<<"Error: energy deposit already exists"<<std::endl;
                }else{
                    energy_deposit_AHCAL_data[index*40*18*18+GetBin1d_AHCAL(ID_X-1,ID_Y-1,ID_Z-1)]=tmp_energy_digi;
                }
                total_energy_AHCAL_data[index]+=tmp_energy_digi;
            }
        }
        // Write the data to the HDF5 file
        hsize_t offset[1] = { static_cast<hsize_t>(start) };
        hsize_t count[1] = { static_cast<hsize_t>(current_batch_size) };
        dataspace.selectHyperslab(H5S_SELECT_SET, count, offset);

        DataSpace memspace(1, count);
        dataset_ftagNulabel.write(ftagNulabel_data.data(), PredType::NATIVE_INT, memspace, dataspace);
        dataset_ParticleEnergy.write(ParticleEnergy_data.data(), PredType::NATIVE_FLOAT, memspace, dataspace); 
        dataset_Interaction_x.write(Interaction_x_data.data(), PredType::NATIVE_FLOAT, memspace, dataspace);
        dataset_Interaction_y.write(Interaction_y_data.data(), PredType::NATIVE_FLOAT, memspace, dataspace);
        dataset_Interaction_z.write(Interaction_z_data.data(), PredType::NATIVE_FLOAT, memspace, dataspace);
        dataset_total_energy_SciW.write(total_energy_SciW_data.data(), PredType::NATIVE_FLOAT, memspace, dataspace);
        dataset_total_energy_AHCAL.write(total_energy_AHCAL_data.data(), PredType::NATIVE_FLOAT, memspace, dataspace);
        hsize_t dims_SciW_mem[4] = { current_batch_size, 32, 5, 42 };
        hsize_t dims_AHCAL_mem[4] = { current_batch_size, 40, 18, 18 };
        DataSpace memspace_SciW(4, dims_SciW_mem);
        DataSpace memspace_AHCAL(4, dims_AHCAL_mem);
        hsize_t offset_SciW[4] = { static_cast<hsize_t>(start), 0, 0, 0 };
        hsize_t offset_AHCAL[4] = { static_cast<hsize_t>(start), 0, 0, 0 };
        dataspace_SciW.selectHyperslab(H5S_SELECT_SET, dims_SciW_mem, offset_SciW);
        dataspace_AHCAL.selectHyperslab(H5S_SELECT_SET, dims_AHCAL_mem, offset_AHCAL);
        dataset_energy_deposit_SciW.write(energy_deposit_SciW_data.data(), PredType::NATIVE_FLOAT, memspace_SciW, dataspace_SciW);
        dataset_energy_deposit_AHCAL.write(energy_deposit_AHCAL_data.data(), PredType::NATIVE_FLOAT, memspace_AHCAL, dataspace_AHCAL);

        std::cout << "Processed entries: " << start << " to " << end << std::endl;
    }

    // Close the ROOT file
    root_file->Close();
    h5_file.close();
}

int main(int argc,char** argv){
    std::string root_file_path = argv[1];
    std::string tree_name = "treeEvt";
    std::string h5_file_path = argv[2];
    convert_caloroot_to_h5(root_file_path, tree_name, h5_file_path);
    return 0;
}
//g++ -o convert_withdigi convert_withdigi.cpp `root-config --cflags --libs` -lhdf5_cpp -lhdf5