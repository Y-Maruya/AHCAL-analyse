#include "RawtoRoot.h"
#include "Global.h"
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <algorithm>
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
#include "TRandom.h"
#include <TSpectrum.h>
#include "TLegend.h"
#include "TLine.h"
#include "TVirtualFitter.h"
#include "TGraphErrors.h"
#include "TGraph.h"
#include "TGaxis.h"
#include "TH3D.h"
#include "TLatex.h"
#include "TBox.h"
// #include </afs/ihep.ac.cn/users/s/shiyk/YukunToolBox/Root.h>
//#include "Event.h"
int layer,chip,channel;
using namespace std;
char char_tmp[200];
Int_t main(int argc,char *argv[])
{
    double start = clock();
    raw2Root tw;
    tw.Test(argv[1],argv[2],argv[3],argv[4],argv[5],stoi(argv[6]),stoi(argv[7]));
    double end = clock();
    cout<<"end of RawToRoot : Time : "<<(end-start)/CLOCKS_PER_SEC<<endl;
    return 0;
}
double GetMinXWithContent(TH1* h) {
    for (int i = 1; i <= h->GetNbinsX(); ++i) {
        if (h->GetBinContent(i) > 0) {
            return h->GetBinLowEdge(i);  // または h->GetBinCenter(i)
        }
    }
    return -999; // 内容がない場合など
}
double GetMaxXWithContent(TH1* h) {
    for (int i = h->GetNbinsX(); i >= 1; --i) {
        if (h->GetBinContent(i) > 0) {
            return h->GetBinLowEdge(i) + h->GetBinWidth(i);  // または h->GetBinCenter(i)
        }
    }
    return -999; // 内容がない場合など
}

enum ChannelCharacteristics{
    TooHighADC = 1,
    ThBad1peek = 2,
    ThBad2peek = 5,
    ThGood1peek = 9,
    ThGood2peek = 13,
    NoData = 17
};
int CriteriaForhighADC = 1000;
int raw2Root::Test(string str_dat,string str_ped,string str_dac,string str_MIP,string output_file, int trigger_layer0, int trigger_layer1) {
    //string str_root=find_datname(str_in);
    //string str_out=outputDir+"/"+"cos_ana.root";
    string str_out=output_file;
    TFile *fin,*fout;
    TTree *tree_in,*tree_out;
    double ped_time[Layer_No][chip_No][channel_No];
    double ped_charge[Layer_No][chip_No][channel_No];
    double gain_ratio[Layer_No][chip_No][channel_No];
    double gain_plat[Layer_No][chip_No][channel_No];
    double gain_intercept[Layer_No][chip_No][channel_No];
    double MIP[Layer_No][chip_No][channel_No];
    double hitE,hitE_layer[Layer_No],hitNo_layer[Layer_No];
    double Edep=0;
    double MIP_E=0.461;//MeV
    double SwitchPoint=500;
    const double ref_ped_time=390;
    const double ref_ped_charge=384;
    const double ref_MIP=344.3;
    const double ref_gain_ratio=26;
    const int lowgain_plat=2000;
    int Select_EventNo=0;
    int HitNo=0;
    int CellID=0;
    float slope=0;
    float intercept = 0;
    double MPV = 0;
    int entries = 0;
    int Tag = 0;
    float plat = 0;
    double pedestal_time=0;
    double pedestal_charge=0;
    double Layer_E[Layer_No]={0};
    TH1D *h_Edep;
    TH2D *h2_HitE_Layer;
    TH2D *h2_HitMap;
    sprintf(char_tmp,"Energy deposition");
    h_Edep = new TH1D(char_tmp,char_tmp,1000,0,3);
    sprintf(char_tmp,"Layer-HitE");
    h2_HitE_Layer = new TH2D(char_tmp,char_tmp,100,0,100,40,0,40);
    sprintf(char_tmp,"Hit Map");
    h2_HitMap = new TH2D(char_tmp,char_tmp,18,-HBU_X*3/2.,HBU_X*3/2.,18,-HBU_Y/2.,HBU_Y/2.);
    //read ped
    fin = TFile::Open(str_ped.c_str(),"READ");
    if (!fin){
        cout<<"cant open "<<str_ped<<endl;
        return 0;
    }
    tree_in = (TTree*)fin->Get("pedestal");
    if(!tree_in){
        cout<<"cant get tree pedestal"<<endl;
        return 0;
    }
    tree_in->SetBranchAddress("cellid",&CellID);
    //tree_in->SetBranchAddress("time_peak",&pedestal_time);
    //tree_in->SetBranchAddress("charge_peak",&pedestal_charge);
    tree_in->SetBranchAddress("highgain_peak",&pedestal_time);
    tree_in->SetBranchAddress("lowgain_peak",&pedestal_charge);
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            for (int i_chan = 0; i_chan < channel_No; ++i_chan){
                ped_time[i_layer][i_chip][i_chan]=-1;
                ped_charge[i_layer][i_chip][i_chan]=-1;
                MIP[i_layer][i_chip][i_chan]=-1;
                gain_ratio[i_layer][i_chip][i_chan]=-1;
            }
        }
    }
    for (int i = 0; i < tree_in->GetEntries(); ++i){
        tree_in->GetEntry(i);
        decode_cellid(CellID,layer,chip,channel);
        //cout<<layer<<" "<<chip<<" "<<channel<<" "<<pedestal_time<<" "<<pedestal_charge<<endl;
        ped_time[layer][chip][channel]=pedestal_time;
        ped_charge[layer][chip][channel]=pedestal_charge;
    }
    tree_in->Delete();
    fin->Close();
    //read dac
    fin = TFile::Open(str_dac.c_str(),"READ");
    if (!fin){
        cout<<"cant open "<<str_dac<<endl;
        return 0;
    }
    //tree_in = (TTree*)fin->Get("calib");
    tree_in = (TTree*)fin->Get("dac");
    if(!tree_in){
        cout<<"cant get tree dac"<<endl;
        return 0;
    }
    tree_in->SetBranchAddress("cellid",&CellID);
    tree_in->SetBranchAddress("slope",&slope);
    tree_in->SetBranchAddress("plat",&plat);
    // tree_in->SetBranchAddress("intercept",&intercept);
    for (int i = 0; i < tree_in->GetEntries(); ++i){
        tree_in->GetEntry(i);
        decode_cellid(CellID,layer,chip,channel);
        //cout<<layer<<" "<<chip<<" "<<channel<<" "<<slope<<" "<<endl;
        gain_ratio[layer][chip][channel]=slope;
        gain_plat[layer][chip][channel]=plat;
        // gain_intercept[layer][chip][channel] = intercept;
        if (gain_ratio[layer][chip][channel] < 10 || gain_ratio[layer][chip][channel] > 50)
            cout << CellID << " abnormal gain ratio " << layer << " " << chip << " " << channel << " " << slope << endl;
    }
    tree_in->Delete();
    fin->Close();
    //read MIP
    fin = TFile::Open(str_MIP.c_str(),"READ");
    if (!fin){
        cout<<"cant open "<<str_MIP<<endl;
        return 0;
    }
    tree_in = (TTree*)fin->Get("MIP_Calibration");
    if(!tree_in){
        cout<<"cant get MIP tree"<<endl;
        return 0;
    }
    tree_in->SetBranchAddress("CellID",&CellID);
    tree_in->SetBranchAddress("MPV",&MPV);
    tree_in->SetBranchAddress("Tag",&Tag);
    //tree_in->SetBranchAddress("mpv",&MPV);
    for (int i = 0; i < tree_in->GetEntries(); ++i){
        tree_in->GetEntry(i);
        decode_cellid(CellID,layer,chip,channel);
        //MIP[layer][chip][channel]=MPV - ped_time[layer][chip][channel];
        MIP[layer][chip][channel]=MPV;
        if (Tag!=1)
            MIP[layer][chip][channel] = ref_MIP;
        // cout<<layer<<" "<<chip<<" "<<channel<<" "<<MPV<<endl;
        if (MIP[layer][chip][channel] < 200)
            cout << "abnormal MIP " << layer << " " << chip << " " << channel << " " << MPV << endl;
    }
    tree_in->Delete();
    fin->Close();
    //read dat
    fin = TFile::Open(str_dat.c_str(),"READ");
    if (!fin){
        cout<<"cant open "<<str_dat<<endl;
        return 0;
    }
    cout<<"Read TTree "<<endl;
    tree_in = (TTree*)fin->Get("Raw_Hit");
    cout<<"Read TTree Over"<<endl;
    ReadTreeBranch(tree_in);
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            for (int i_chan = 0; i_chan < channel_No; ++i_chan){
                // ped_time[i_layer][i_chip][i_chan] += gain_intercept[i_layer][i_chip][i_chan];
                // ped_charge[i_layer][i_chip][i_chan] -= gain_intercept[i_layer][i_chip][i_chan]/gain_ratio[i_layer][i_chip][i_chan];
                if (ped_time[i_layer][i_chip][i_chan] < 0)ped_time[i_layer][i_chip][i_chan] = ref_ped_time;
                if(ped_charge[i_layer][i_chip][i_chan]<0) ped_charge[i_layer][i_chip][i_chan]=ref_ped_charge;
                // if(MIP[i_layer][i_chip][i_chan]<100) MIP[i_layer][i_chip][i_chan]=ref_MIP;
                if(gain_ratio[i_layer][i_chip][i_chan]<0) gain_ratio[i_layer][i_chip][i_chan]=ref_gain_ratio;
                //cout<<i_layer<<" "<<i_chip<<" "<<i_chan<<endl;
                //cout<<ped_time[i_layer][i_chip][i_chan]<<" "<<ped_time[i_layer][i_chip][i_chan]<<" "<<MIP[i_layer][i_chip][i_chan]<<" "<<gain_ratio[i_layer][i_chip][i_chan]<<endl;
            }
        }
    }
    int max_triggerID = 0;
    TH1D *h_triggerID = new TH1D("h_triggerID","h_triggerID",1e9,0,1e9);
    tree_in->Draw("TriggerID>>h_triggerID");
    max_triggerID = GetMaxXWithContent(h_triggerID);
    cout<<"max_triggerID = "<<max_triggerID<<endl;
    fout = TFile::Open(str_out.c_str(),"RECREATE");
    if (!fout){
        cout<<"cant open "<<str_out<<endl;
        return 0;
    }

    TH2I *h2_Map_channel = new TH2I("h2_Map_channel","h2_Map_channel;x [mm];y [mm]",18,-360,360,18,-360,360);
    TH2I *h2_Map_chip = new TH2I("h2_Map_chip","h2_Map_chip;x [mm];y [mm]",18,-360,360,18,-360,360);
    gStyle->SetHistMinimumZero();
    // h2_Map_channel->SetGrid();
    // h2_Map_chip->SetGrid();
    h2_Map_channel->SetTitle("Channel Map");
    h2_Map_chip->SetTitle("Chip Map");
    tree_out = new TTree("EventTree","Hits afer energy calibration");
    SetTreeBranch(tree_out);
    TH1D *h_ADC_hittag0[Layer_No][chip_No][channel_No];
    TH2D *h_ADC_TriggerID_hittag0[Layer_No][chip_No][channel_No];
    TH1D *h_ADC_hittag1[Layer_No][chip_No][channel_No];
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            for (int i_chan = 0; i_chan < channel_No; ++i_chan){
                sprintf(char_tmp,"hittag_0_ADC_%d_%d_%d",i_layer,i_chip,i_chan);
                h_ADC_hittag0[i_layer][i_chip][i_chan] = new TH1D(char_tmp,char_tmp,512,0,4096);
                sprintf(char_tmp,"hittag_0_ADC_TriggerID_%d_%d_%d",i_layer,i_chip,i_chan);

                h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan] = new TH2D(char_tmp,char_tmp,100,0, max_triggerID,512,0,4096);
                h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan]->SetDirectory(0);
                h_ADC_hittag0[i_layer][i_chip][i_chan]->SetDirectory(0);
                sprintf(char_tmp,"hittag_1_ADC_%d_%d_%d",i_layer,i_chip,i_chan);
                h_ADC_hittag1[i_layer][i_chip][i_chan] = new TH1D(char_tmp,char_tmp,512,0,4096);
                h_ADC_hittag0[i_layer][i_chip][i_chan]->SetDirectory(0);
                h_ADC_hittag1[i_layer][i_chip][i_chan]->SetDirectory(0);
                if (i_layer == 0){
                    h2_Map_channel->Fill(Pos_X(i_chan,i_chip),Pos_Y(i_chan,i_chip),i_chan);
                    h2_Map_chip->Fill(Pos_X(i_chan,i_chip),Pos_Y(i_chan,i_chip),i_chip);
                }
            }
        }
    }
    std::cout << "pedestal time and charge:" << std::endl;
    TH2D *h2_trigger_layer_hit = new TH2D("h2_trigger_layer_hit","h2_trigger_layer_hit",5,-0.5,4.5,5,-0.5,4.5);
    for (int i = 0; i < tree_in->GetEntries(); ++i){
        Edep=0;
        BranchClear();
        if((i%1000)==0)cout<<i<<" out of "<<tree_in->GetEntries()<<endl;
        tree_in->GetEntry(i);
        // if (_Event_Time < 72  || _Event_Time > 76 ) continue; // filter events by time
        // if (_Event_Time > 19200 && _Event_Time < 22800) continue; // filter events by time
        _Event_No=_triggerID;
        // if (_triggerID > 3000) continue; // filter events by trigger ID 
        if (_Event_Time< 1){
            continue;
        }
        _Detector_ID=1;
        int m = 0;
        int trigger_layer_hit[Layer_No]={0};
        for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
            trigger_layer_hit[i_layer]=0;
        }
        for (int i_hit = 0; i_hit < cellID->size(); ++i_hit){
            decode_cellid(cellID->at(i_hit),layer,chip,channel);
            if((hitTag->at(i_hit))==0){
                h_ADC_hittag0[layer][chip][channel]->Fill(HG_Charge->at(i_hit));
                h_ADC_TriggerID_hittag0[layer][chip][channel]->Fill(_triggerID,HG_Charge->at(i_hit));
            }
            else h_ADC_hittag1[layer][chip][channel]->Fill(HG_Charge->at(i_hit));
            if((hitTag->at(i_hit))==0) continue;
            _cellID.push_back(cellID->at(i_hit));
            trigger_layer_hit[layer]++;
            if( (HG_Charge->at(i_hit))-ped_time[layer][chip][channel] < gain_plat[layer][chip][channel]-SwitchPoint )
            {
                hitE=( HG_Charge->at(i_hit) - ped_time[layer][chip][channel] )*MIP_E/MIP[layer][chip][channel];
            }
            // else
            // {
            //     if(LG_Charge->at(i_hit)<800)
            //         hitE=( LG_Charge->at(i_hit) - ped_charge[layer][chip][channel] )*gain_ratio[layer][chip][channel]*MIP_E/MIP[layer][chip][channel];
            //     else
            //     {
            //         hitE = -100;
            //         // hitE = (800 - ped_charge[layer][chip][channel]) * gain_ratio[layer][chip][channel] * MIP_E / MIP[layer][chip][channel];
            //     }
            // } 
            else hitE=( LG_Charge->at(i_hit) - ped_charge[layer][chip][channel] )*gain_ratio[layer][chip][channel]*MIP_E/MIP[layer][chip][channel];
            _Hit_E.push_back(hitE);
            _Hit_X.push_back(Pos_X(channel,chip));
            _Hit_Y.push_back(Pos_Y(channel,chip));
            _Hit_Z.push_back(layer*30);
            // _Hit_Time.push_back(Hit_Time->at(i_hit));
            // cout << "test" << endl;
            Edep += hitE;
            // h2_HitMap->Fill(_Hit_X[i_hit],_Hit_Y[i_hit]);
            h2_HitMap->Fill(_Hit_X[m],_Hit_Y[m]);
            if(hitE>500*MIP_E){
                cout<<hitE/MIP_E<<" high energy alert "<<layer<<" "<<chip<<" "<<channel<<endl;
                cout<<HG_Charge->at(i_hit)<<" "<<MIP[layer][chip][channel]<<" "<<gain_ratio[layer][chip][channel]<<endl;
            }
            m++;
        }
        h2_trigger_layer_hit->Fill(trigger_layer_hit[trigger_layer0],trigger_layer_hit[trigger_layer1]);
        h_Edep->Fill(Edep/1000.);
        for (int i_c = 0; i_c < cherenkov->size(); ++i_c){
            if((cherenkov->size())!=2)cout<<"abnormal cherenkov "<<i<<" "<<cherenkov->size()<<endl;
            _cherenkov.push_back(cherenkov->at(i_c));
        }
        _Digi_Energy=Edep;
        tree_out->Fill();
    }
    fout->cd();
    tree_out->Write();
    h2_HitMap->Write();
    h_Edep->Write();
    TH2I *h2_ChMap = new TH2I("h2_ChMap","h2_ChMap;ChipID;ChannelID",chip_No*Layer_No,0,chip_No*Layer_No,channel_No,0,channel_No);
    TH2D *h2_PedMap = new TH2D("h2_PedMap","h2_PedMap;ChipID;ChannelID",chip_No*Layer_No,0,chip_No*Layer_No,channel_No,0,channel_No);
    TH2D *h2_nominal_PedMap = new TH2D("h2_nominal_PedMap","h2_nominal_PedMap;ChipID;ChannelID",chip_No*Layer_No,0,chip_No*Layer_No,channel_No,0,channel_No);
    TH2D *h2_HitMap_HitTag = new TH2D("h2_HitMap","h2_HitMap;ChipID;ChannelID",chip_No*Layer_No,0,chip_No*Layer_No,channel_No,0,channel_No);
    // TH3D *h3_sum0 = new TH3D("h3_sum0","h3_sum0",Layer_No,0,Layer_No,chip_No,0,chip_No,channel_No,0,channel_No);
    // TH3D *h3_sum1 = new TH3D("h3_sum1","h3_sum1",Layer_No,0,Layer_No,chip_No,0,chip_No,channel_No,0,channel_No);
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        // fout->mkdir(Form("Layer_%d",i_layer));
        // fout->cd(Form("Layer_%d",i_layer));
        TH2D * h2_HitMap_layer = new TH2D(Form("h2_HitMap_layer_%d",i_layer),Form("h2_HitMap_layer_%d;Position X [mm];Position Y [mm]",i_layer),18,-HBU_X*3/2.,HBU_X*3/2.,18,-HBU_Y/2.,HBU_Y/2.);
        h2_HitMap_layer->SetDirectory(0);
        h2_HitMap_layer->SetTitle(Form("Hit Map Layer %d",i_layer));
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            // fout->mkdir(Form("Layer_%d/Chip_%d",i_layer,i_chip));
            // fout->cd(Form("Layer_%d/Chip_%d",i_layer,i_chip));
            for (int i_chan = 0; i_chan < channel_No; ++i_chan){
                // h_ADC_hittag0[i_layer][i_chip][i_chan]->Write();
                // h_ADC_hittag1[i_layer][i_chip][i_chan]->Write();
                h2_PedMap->Fill(i_layer*chip_No+i_chip,i_chan,h_ADC_hittag0[i_layer][i_chip][i_chan]->GetBinCenter(h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximumBin()));
                h2_nominal_PedMap->Fill(i_layer*chip_No+i_chip,i_chan,ped_time[i_layer][i_chip][i_chan]);
                // if (i_chip != 7 || (i_chan != 35 && i_chan != 24)){
                    h2_HitMap_HitTag->Fill(i_layer*chip_No+i_chip,i_chan,h_ADC_hittag1[i_layer][i_chip][i_chan]->GetEntries());
                    h2_HitMap_layer->Fill(Pos_X(i_chan,i_chip),Pos_Y(i_chan,i_chip),h_ADC_hittag1[i_layer][i_chip][i_chan]->GetEntries());
                // }
                if (h_ADC_hittag0[i_layer][i_chip][i_chan]->GetEntries() == 0 && h_ADC_hittag1[i_layer][i_chip][i_chan]->GetEntries() == 0){
                    h2_ChMap->Fill(i_layer*chip_No+i_chip,i_chan,NoData);
                }
                TCanvas *c1 = new TCanvas(Form("c1_%d_%d_%d",i_layer,i_chip,i_chan),Form("c1_%d_%d_%d",i_layer,i_chip,i_chan),800,1800);
                c1->Divide(1,3);
                c1->cd(1);
                h_ADC_hittag0[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 0, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
                double minX_0 = GetMinXWithContent(h_ADC_hittag0[i_layer][i_chip][i_chan]);
                double maxX_0 = GetMaxXWithContent(h_ADC_hittag0[i_layer][i_chip][i_chan]);
                double minX_1 = GetMinXWithContent(h_ADC_hittag1[i_layer][i_chip][i_chan]);
                double maxX_1 = GetMaxXWithContent(h_ADC_hittag1[i_layer][i_chip][i_chan]);
                double ped = h_ADC_hittag0[i_layer][i_chip][i_chan]->GetBinCenter(h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximumBin());
                if (maxX_0 > CriteriaForhighADC && h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == 0){
                    h2_ChMap->Fill(i_layer*chip_No+i_chip,i_chan,TooHighADC);
                }
                h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(min(minX_0,minX_1)-20,max(maxX_0,maxX_1)+20);
                h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan]->GetYaxis()->SetRangeUser(minX_0-20,maxX_0+20);
                h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(min(minX_0,minX_1)-20,max(maxX_0,maxX_1)+20);
                if (maxX_0 > minX_1){
                    // std::cout << "threshold error: " << i_layer << " " << i_chip << " " << i_chan << std::endl;
                    int sum0 = h_ADC_hittag0[i_layer][i_chip][i_chan]->Integral(h_ADC_hittag0[i_layer][i_chip][i_chan]->FindBin(minX_1),h_ADC_hittag0[i_layer][i_chip][i_chan]->FindBin(maxX_0));
                    int sum1 = h_ADC_hittag1[i_layer][i_chip][i_chan]->Integral(h_ADC_hittag1[i_layer][i_chip][i_chan]->FindBin(minX_1),h_ADC_hittag1[i_layer][i_chip][i_chan]->FindBin(maxX_1));
                    int sum_all0 = h_ADC_hittag0[i_layer][i_chip][i_chan]->Integral(h_ADC_hittag0[i_layer][i_chip][i_chan]->FindBin(minX_0),h_ADC_hittag0[i_layer][i_chip][i_chan]->FindBin(maxX_0));
                    int sum_all1 = h_ADC_hittag1[i_layer][i_chip][i_chan]->Integral(h_ADC_hittag1[i_layer][i_chip][i_chan]->FindBin(minX_1),h_ADC_hittag1[i_layer][i_chip][i_chan]->FindBin(maxX_1));
                    // std::cout << "sum0/sum_all0: " << sum0 << " " << sum_all0 << std::endl;
                    // std::cout << "sum1/sum_all1: " << sum1 << " " << sum_all1 << std::endl;
                    // h3_sum0->SetBinContent(i_layer+1,i_chip+1,i_chan+1, double(sum0)/double(sum_all0));
                    // h3_sum1->SetBinContent(i_layer+1,i_chip+1,i_chan+1, double(sum1)/double(sum_all1));
                    if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == 0){
                        if (double(sum0)/double(sum_all0) > 0.3 && double(sum1)/double(sum_all1) > 0.3){
                            if (abs(h_ADC_hittag1[i_layer][i_chip][i_chan]->GetBinCenter(h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximumBin()) - ped )< 20){
                                h2_ChMap->Fill(i_layer*chip_No+i_chip,i_chan,ThBad2peek);
                            }else{
                                h2_ChMap->Fill(i_layer*chip_No+i_chip,i_chan,ThBad1peek);
                            }
                        }else if (double(sum0)/double(sum_all0) > 0.3 && maxX_0 < CriteriaForhighADC){
                            std::cout << "sum0/sum_all0: " << double(sum0)/double(sum_all0) << "not too high ADC" << std::endl;
                        }else if (double(sum1)/double(sum_all1) > 0.3 && maxX_1 < CriteriaForhighADC){
                            std::cout << "sum1/sum_all1: " << double(sum1)/double(sum_all1) << "not too high ADC" << std::endl;
                        }else{
                            // h2_ChMap->Fill(i_layer*chip_No+i_chip,i_chan,ThGood1peek);
                        }
                    }
                }
                if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == 0){
                    if (h_ADC_hittag1[i_layer][i_chip][i_chan]->GetBinCenter(h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximumBin()) - ped < MIP[layer][chip][channel] / 2){
                        h2_ChMap->Fill(i_layer*chip_No+i_chip,i_chan,ThGood2peek);
                    }else{
                        h2_ChMap->Fill(i_layer*chip_No+i_chip,i_chan,ThGood1peek);
                    }
                }
                // if (i_layer==6 && i_chip == 6 || i_layer == trigger_layer0 || i_layer == trigger_layer1){
                //     TLine* h_ped_line = new TLine(ped_time[i_layer][chip][channel],0,ped_time[i_layer][chip][channel],h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximum());
                //     TLine* h_mip_line = new TLine(MIP[i_layer][chip][channel]+ped_time[i_layer][chip][channel],0,MIP[i_layer][chip][channel]+ped_time[i_layer][chip][channel],h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximum());
                //     h_ped_line->SetLineColor(kBlack);
                //     h_ped_line->SetLineStyle(2);
                //     h_ped_line->SetLineWidth(2);
                //     h_mip_line->SetLineColor(kGreen);
                //     h_mip_line->SetLineStyle(2);
                //     h_mip_line->SetLineWidth(2);
                //     // h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->GetXmin()-100,h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->GetXmax()+100);
                //     // h_ADC_hittag0[i_layer][i_chip][i_chan]->SetBins(h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->GetXmax()- h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->GetXmin() +200,h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->GetXmin()-100,h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->GetXmax()+100);
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetTitle("ADC");
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->GetYaxis()->SetTitle("Counts");
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->SetLineColor(kRed);
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->Draw();
                //     h_ADC_hittag1[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 1, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
                //     h_ADC_hittag1[i_layer][i_chip][i_chan]->Draw("histsame");
                //     c1->cd(2);
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 0, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetTitle("ADC");
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->GetYaxis()->SetTitle("Counts");
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->SetLineColor(kRed);
                //     h_ADC_hittag0[i_layer][i_chip][i_chan]->Draw();
                //     c1->cd(3);
                //     h_ADC_hittag1[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 1, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
                //     h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->SetTitle("ADC");
                //     h_ADC_hittag1[i_layer][i_chip][i_chan]->GetYaxis()->SetTitle("Counts");
                //     h_ADC_hittag1[i_layer][i_chip][i_chan]->SetLineColor(kBlue);
                //     h_ADC_hittag1[i_layer][i_chip][i_chan]->Draw();
                //     h_ped_line->Draw("same");
                //     h_mip_line->Draw("same");
                //     c1->Update();
                //     c1->Modified();
                //     c1->Write();
                //     // mkdir
                //     if (gSystem->AccessPathName(Form("Layer_%d/Chip_%d",i_layer,i_chip)))
                //     {
                //         gSystem->mkdir(Form("Layer_%d/Chip_%d",i_layer,i_chip),true);
                //     }
                //     c1->SaveAs(Form("Layer_%d/Chip_%d/hittag_%d_%d_%d.png",i_layer,i_chip,i_layer,i_chip,i_chan));
                //     c1->Write();
                //     TCanvas *c2 = new TCanvas(Form("c2_%d_%d_%d",i_layer,i_chip,i_chan),Form("c2_%d_%d_%d",i_layer,i_chip,i_chan),800,600);
                //     // c2->SetRightMargin(0.20);
                //     h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 0, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
                //     h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetTitle("Trigger ID");
                //     h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan]->GetYaxis()->SetTitle("ADC");
                //     h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan]->SetStats(0);
                //     h_ADC_TriggerID_hittag0[i_layer][i_chip][i_chan]->Draw("colz");
                //     c2->Update();
                //     c2->Modified();
                //     c2->Write();
                //     if (gSystem->AccessPathName(Form("Layer_%d/Chip_%d",i_layer,i_chip)))
                //     {
                //         gSystem->mkdir(Form("Layer_%d/Chip_%d",i_layer,i_chip),true);
                //     }
                //     c2->SaveAs(Form("Layer_%d/Chip_%d/hittag_0_ADC_TriggerID_%d_%d_%d.png",i_layer,i_chip,i_layer,i_chip,i_chan));
                // }
            }
        }
        h2_HitMap_layer->Write();
        TCanvas *c3 = new TCanvas(Form("c3_%d",i_layer),Form("c3_%d",i_layer),800,600);
        c3->SetRightMargin(0.20);
        h2_HitMap_layer->SetTitle(Form("Hit Map Layer %d",i_layer));
        h2_HitMap_layer->GetXaxis()->SetTitle("Position X [mm]");
        h2_HitMap_layer->GetYaxis()->SetTitle("Position Y [mm]");
        h2_HitMap_layer->GetZaxis()->SetTitle("Hit Counts");
        h2_HitMap_layer->SetStats(0);
        c3->SetLogz();
        h2_HitMap_layer->SetMarkerSize(0.8); // Adjust text size in bins
        h2_HitMap_layer->Draw("colz text");
        c3->Update();
        c3->Modified();
        c3->Write();
        if (gSystem->AccessPathName(Form("Layer_%d",i_layer)))
        {
            gSystem->mkdir(Form("Layer_%d",i_layer),true);
        }
        c3->SaveAs(Form("Layer_%d/h2_HitMap_layer_%d.png",i_layer,i_layer));
        // h2_Map_channel->Write();
    }
    TCanvas *c4 = new TCanvas("c4","c4",3000,600);
    c4->SetRightMargin(0.20);
    h2_HitMap_HitTag->SetTitle("Hit Map");
    h2_HitMap_HitTag->GetXaxis()->SetTitle("Layer*Chip");
    h2_HitMap_HitTag->GetYaxis()->SetTitle("Channel");
    h2_HitMap_HitTag->GetZaxis()->SetTitle("Hit Counts");
    h2_HitMap_HitTag->SetStats(0);
    c4->SetLogz();
    h2_HitMap_HitTag->Draw("colz");
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
        // Draw vertical line for each layer boundary
        double x = i_layer * chip_No;
        TLine* line = new TLine(x, 0, x, channel_No);
        line->SetLineColor(kBlack);
        line->SetLineStyle(2);
        line->SetLineWidth(2);
        line->Draw();

        // Add layer label
        TLatex* latex = new TLatex(x + chip_No / 2.0, channel_No + 1, Form("%d", i_layer));
        latex->SetTextAlign(22);
        latex->SetTextSize(0.025);
        latex->Draw();
    }
    TLatex *text = new TLatex(0,channel_No+2,"Layer");
    text->SetTextSize(0.03);
    text->SetTextAlign(22);
    text->Draw();
    c4->Update();
    c4->Modified();
    c4->Write();
    c4->SaveAs("h2_HitMap.png");
    h2_PedMap->GetZaxis()->SetRangeUser(200,500);
    h2_PedMap->SetTitle("Pedestal Map");
    h2_PedMap->GetXaxis()->SetTitle("Layer*Chip");
    h2_PedMap->GetYaxis()->SetTitle("Channel");
    h2_PedMap->GetZaxis()->SetTitle("Pedestal ADC");
    h2_PedMap->SetStats(0);
    TCanvas *c5 = new TCanvas("c5","c5",3000,600);
    c5->SetRightMargin(0.20);
    h2_PedMap->Draw("colz");
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
        // Draw vertical line for each layer boundary
        double x = i_layer * chip_No;
        TLine* line = new TLine(x, 0, x, channel_No);
        line->SetLineColor(kBlack);
        line->SetLineStyle(2);
        line->SetLineWidth(2);
        line->Draw();

        // Add layer label
        TLatex* latex = new TLatex(x + chip_No / 2.0, channel_No + 1, Form("%d", i_layer));
        latex->SetTextAlign(22);
        latex->SetTextSize(0.025);
        latex->Draw();
    }
    TLatex *text2 = new TLatex(0,channel_No+2,"Layer");
    text2->SetTextSize(0.03);
    text2->SetTextAlign(22);
    text2->Draw();
    c5->Update();
    c5->Modified();
    c5->Write();
    c5->SaveAs("h2_PedMap.png");
    TCanvas *c6 = new TCanvas("c6","c6",3000,600);
    c6->SetRightMargin(0.20);
    h2_nominal_PedMap->SetTitle("Nominal Pedestal Map");
    h2_nominal_PedMap->GetXaxis()->SetTitle("Layer*Chip");
    h2_nominal_PedMap->GetYaxis()->SetTitle("Channel");
    h2_nominal_PedMap->GetZaxis()->SetTitle("Nominal Pedestal ADC");
    h2_nominal_PedMap->SetStats(0);
    h2_nominal_PedMap->GetZaxis()->SetRangeUser(200,500);
    h2_nominal_PedMap->Draw("colz");
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
        // Draw vertical line for each layer boundary
        double x = i_layer * chip_No;
        TLine* line = new TLine(x, 0, x, channel_No);
        line->SetLineColor(kBlack);
        line->SetLineStyle(2);
        line->SetLineWidth(2);
        line->Draw();

        // Add layer label
        TLatex* latex = new TLatex(x + chip_No / 2.0, channel_No + 1, Form("%d", i_layer));
        latex->SetTextAlign(22);
        latex->SetTextSize(0.025);
        latex->Draw();
    }
    TLatex *text3 = new TLatex(0,channel_No+2,"Layer");
    text3->SetTextSize(0.03);
    text3->SetTextAlign(22);
    text3->Draw();
    c6->Update();
    c6->Modified();
    c6->Write();
    c6->SaveAs("h2_nominal_PedMap.png");
    TCanvas *c0 = new TCanvas("c0","c0",3000,600);
    c0->SetRightMargin(0.20);
    h2_ChMap->SetTitle("Characteristics Map");
    h2_ChMap->GetXaxis()->SetTitle("Layer*Chip");
    h2_ChMap->GetYaxis()->SetTitle("Channel");
    h2_ChMap->GetZaxis()->SetTitle("Characteristics");
    h2_ChMap->SetStats(0);
    TLegend *leg = new TLegend(0.8,0.3,0.9,0.9);
    h2_ChMap->Draw();
                int cla[7] = {0,0,0,0,0,0,0};
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            for (int i_chan = 0; i_chan < channel_No; ++i_chan){
                // for (int en = 0; en < 6; ++en){
                    if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == ChannelCharacteristics::TooHighADC){
                        TBox *box = new TBox(i_layer*chip_No+i_chip,i_chan,i_layer*chip_No+i_chip+1,i_chan+1);
                        box->SetFillColor(kRed);
                        box->Draw();
                        if (cla[0] == 0){
                            leg->AddEntry(box,"Too High ADC","f");
                            cla[0] = 1;
                        }
                    }else if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == ChannelCharacteristics::ThBad1peek){
                        TBox *box = new TBox(i_layer*chip_No+i_chip,i_chan,i_layer*chip_No+i_chip+1,i_chan+1);
                        box->SetFillColor(kOrange);
                        box->Draw();
                        // leg->AddEntry(box,"Threshold Bad 1 peek","f");
                        if (cla[1] == 0){
                            leg->AddEntry(box,"Threshold Bad 1 peek","f");
                            cla[1] = 1;
                        }
                    }else if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == ChannelCharacteristics::ThBad2peek){
                        TBox *box = new TBox(i_layer*chip_No+i_chip,i_chan,i_layer*chip_No+i_chip+1,i_chan+1);
                        box->SetFillColor(kYellow);
                        box->Draw();
                        // leg->AddEntry(box,"Threshold Bad 2 peek","f");
                        if (cla[2] == 0){
                            leg->AddEntry(box,"Threshold Bad 2 peek","f");
                            cla[2] = 1;
                        }
                    }else if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == ChannelCharacteristics::ThGood1peek){
                        TBox *box = new TBox(i_layer*chip_No+i_chip,i_chan,i_layer*chip_No+i_chip+1,i_chan+1);
                        box->SetFillColor(kGreen);
                        box->Draw();
                        if (cla[3] == 0){
                            leg->AddEntry(box,"Threshold Good 1 peek","f");
                            cla[3] = 1;
                        }
                        // leg->AddEntry(box,"Threshold Good 1 peek","f");
                    }else if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == ChannelCharacteristics::ThGood2peek){
                        TBox *box = new TBox(i_layer*chip_No+i_chip,i_chan,i_layer*chip_No+i_chip+1,i_chan+1);
                        box->SetFillColor(kCyan);
                        box->Draw();
                        // leg->AddEntry(box,"Threshold Good 2 peek","f");
                        if (cla[4] == 0){
                            leg->AddEntry(box,"Threshold Good 2 peek","f");
                            cla[4] = 1;
                        }
                    }else if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == ChannelCharacteristics::NoData){
                        TBox *box = new TBox(i_layer*chip_No+i_chip,i_chan,i_layer*chip_No+i_chip+1,i_chan+1);
                        box->SetFillColor(kGray);
                        box->Draw();
                        // leg->AddEntry(box,"No Data","f");
                        if (cla[5] == 0){
                            leg->AddEntry(box,"No Data","f");
                            cla[5] = 1;
                        }
                    }else if (h2_ChMap->GetBinContent(i_layer*chip_No+i_chip+1,i_chan+1) == 0){
                        TBox *box = new TBox(i_layer*chip_No+i_chip,i_chan,i_layer*chip_No+i_chip+1,i_chan+1);
                        box->SetFillColor(kMagenta);
                        box->Draw();
                        // leg->AddEntry(box,"Not Classified","f");
                        if (cla[6] == 0){
                            leg->AddEntry(box,"Not Classified","f");
                            cla[6] = 1;
                        }
                    }else{
                        std::cout << "abnormal characteristics " << i_layer << " " << i_chip << " " << i_chan << std::endl;
                    }
                // }
            }
        }
    }
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
        // Draw vertical line for each layer boundary
        double x = i_layer * chip_No;
        TLine* line = new TLine(x, 0, x, channel_No);
        line->SetLineColor(kBlack);
        line->SetLineStyle(2);
        line->SetLineWidth(2);
        line->Draw();

        // Add layer label
        TLatex* latex = new TLatex(x + chip_No / 2.0, channel_No + 1, Form("%d", i_layer));
        latex->SetTextAlign(22);
        latex->SetTextSize(0.025);
        latex->Draw();
    }
    TLatex *text4 = new TLatex(0,channel_No+2,"Layer");
    text4->SetTextSize(0.03);
    text4->SetTextAlign(22);
    text4->Draw();
    leg->SetBorderSize(0);
    leg->SetFillColor(0);
    leg->SetTextSize(0.03);
    leg->Draw();
    // c0->SetLogz();
    c0->SaveAs("h2_ChMap.png");
    TH2I *h2_event = new TH2I("h2_event","h2_event",Layer_No,0,Layer_No,chip_No,0,chip_No);
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            h2_event->Fill(i_layer,i_chip, h_ADC_hittag0[i_layer][i_chip][0]->GetEntries()+h_ADC_hittag1[i_layer][i_chip][0]->GetEntries());
            if (h_ADC_hittag0[i_layer][i_chip][0]->GetEntries() + h_ADC_hittag1[i_layer][i_chip][0]->GetEntries() != h_ADC_hittag0[i_layer][i_chip][1]->GetEntries() + h_ADC_hittag1[i_layer][i_chip][1]->GetEntries()){
                cout << "abnormal event " << i_layer << " " << i_chip << endl;
            }
        }
    }
    h2_event->Write();
    h2_event->SaveAs("h2_event.root");
    TCanvas *c3 = new TCanvas("c3","c3",800,600);
    h2_event->SetTitle("Event");
    h2_event->GetXaxis()->SetTitle("Layer");
    h2_event->GetYaxis()->SetTitle("Chip");
    h2_event->Draw("COLZ");
    // h2_event->GetZaxis()->Set
    // c3->SetLogz();
    c3->SaveAs("h2_event.png");
    c3->SetLogz();
    c3->SaveAs("h2_event_logz.png");
    // c3->SetGrid();?
    gStyle->SetOptStat(0);
    h2_Map_channel->Write();
    h2_Map_channel->Draw("text");
    c3->SaveAs("h2_Map_channel.png");
    h2_Map_channel->SaveAs("h2_Map_channel.root");
    h2_Map_chip->Write();
    h2_Map_chip->Draw("text");
    h2_Map_chip->SaveAs("h2_Map_chip.root");
    c3->SaveAs("h2_Map_chip.png");
    gStyle->SetOptStat(1111);
    // h3_sum0->Write();
    // h3_sum1->Write();
    // h3_sum0->SaveAs("h3_sum0.root");
    // h3_sum1->SaveAs("h3_sum1.root");
    h2_trigger_layer_hit->Write();
    h2_trigger_layer_hit->SaveAs("h2_trigger_layer_hit.root");
    TCanvas *c2 = new TCanvas("c2","c2",800,600);
    h2_trigger_layer_hit->SetTitle("Trigger Layer Hit");
    h2_trigger_layer_hit->GetXaxis()->SetTitle("# of Hit in Layer 8");
    h2_trigger_layer_hit->GetYaxis()->SetTitle("# of Hit in Layer 32");
    h2_trigger_layer_hit->GetZaxis()->SetTitle("Counts");
    h2_trigger_layer_hit->SetStats(0);
    h2_trigger_layer_hit->Draw("COLZ");
    c2->SetLogz();
    c2->SaveAs("h2_trigger_layer_hit.png");
    // h2_trigger_layer_hit->SaveAs("h2_trigger_layer_hit.png");
    fout->Close();
    return 1;
}
