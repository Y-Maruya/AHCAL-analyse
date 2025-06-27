#include "RawtoRoot.h"
#include "Global.h"
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <algorithm>
#include <stdlib.h>
#include <TFile.h>
#include <TTree.h>
#include <TLatex.h>
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
#include "TEfficiency.h"
// #include </afs/ihep.ac.cn/users/s/shiyk/YukunToolBox/Root.h>
//#include "Event.h"
int layer,chip,channel;
using namespace std;
char char_tmp[200];
Int_t main(int argc,char *argv[])
{
    double start = clock();
    raw2Root tw;
    tw.forMuon(argv[1],argv[2],argv[3],argv[4],argv[5]);
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
int ExcludeCh(int layer, int chip, int channel){
    if (layer == 0 && chip == 0) return 1;
    if (layer == 0 && chip == 1) return 1;
    if (chip == 7 && channel == 35) return 1;
    return 0;
}
double z_layer_cosmic(int layer) {
    return (layer/2) * 80.0 + (layer % 2) * 20.0; 
} 
std::tuple <double, double, double, int> FitMuonTrack(TH2D* h2_display) {
    int nHits = 0;
    std::vector<double> x;
    std::vector<double> z;
    std::vector<double> ex;
    std::vector<double> ez;
    for (int i = 1; i <= h2_display->GetNbinsX(); ++i) {
        for (int j = 1; j <= h2_display->GetNbinsY(); ++j) {
            if (h2_display->GetBinContent(i,j) > 0) {
                nHits++;
                double z_val = h2_display->GetXaxis()->GetBinCenter(i);
                double x_val = h2_display->GetYaxis()->GetBinCenter(j);
                x.push_back(x_val);
                z.push_back(z_val);
                ex.push_back(40./std::sqrt(12.0));
                ez.push_back(3./std::sqrt(12.0));
            }
        }
    }
    double x1[nHits];
    double z1[nHits];
    double ex1[nHits];
    double ez1[nHits];
    for (int i = 0; i < nHits; ++i) {
        x1[i] = x[i];
        z1[i] = z[i];
        ex1[i] = ex[i];
        ez1[i] = ez[i];
    }
    TGraphErrors* gr = new TGraphErrors(nHits, z1, x1, ez1, ex1);
    gr->SetTitle("Muon Track Fit;Z [mm];X [mm]");
    gr->SetMarkerStyle(0);
    gr->SetMarkerSize(0);
    TF1* fitLine = new TF1("fitLine", "[0]*x + [1]", 0, 1600);
    gr->Fit(fitLine, "Q");
    gStyle->SetOptStat(0);
    gStyle->SetStatX(1.0);
    gStyle->SetStatY(0.9);
    // h2_display->Draw("COLZ");
    // // gr->Draw("goffsame"); 
    // fitLine->Draw("same");
    // TLatex *latex = new TLatex();
    // latex->SetTextSize(0.03);
    // latex->SetTextColor(kRed);
    // latex->SetNDC();
    // latex->DrawLatex(0.8, 0.9, Form("Slope: %.2f", fitLine->GetParameter(0)));
    // latex->DrawLatex(0.8, 0.85, Form("Intercept: %.2f", fitLine->GetParameter(1)));
    // latex->DrawLatex(0.8, 0.8, Form("Chi2/NDF: %.2f", fitLine->GetChisquare()/fitLine->GetNDF()));
    // latex->DrawLatex(0.8, 0.75, Form("NDF: %d", fitLine->GetNDF()));
    // latex->DrawLatex(0.8, 0.7, Form("NHit: %d", nHits));
    std::tuple <double, double, double, int> result;
    result = std::make_tuple(fitLine->GetParameter(0), fitLine->GetParameter(1), fitLine->GetChisquare()/fitLine->GetNDF(), nHits);
    return result;
}
int raw2Root::forMuon(string str_dat,string str_ped,string str_dac,string str_MIP,string output_file){
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
    fout = TFile::Open(str_out.c_str(),"RECREATE");
    if (!fout){
        cout<<"cant open "<<str_out<<endl;
        return 0;
    }
    tree_out = new TTree("EventTree","Hits afer energy calibration");
    SetTreeBranch(tree_out);
    TH1D *h_ADC_hittag0[Layer_No][chip_No][channel_No];
    TH1D *h_ADC_hittag1[Layer_No][chip_No][channel_No];
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            for (int i_chan = 0; i_chan < channel_No; ++i_chan){
                sprintf(char_tmp,"hittag_0_ADC_%d_%d_%d",i_layer,i_chip,i_chan);
                h_ADC_hittag0[i_layer][i_chip][i_chan] = new TH1D(char_tmp,char_tmp,4096,0,4096);
                sprintf(char_tmp,"hittag_1_ADC_%d_%d_%d",i_layer,i_chip,i_chan);
                h_ADC_hittag1[i_layer][i_chip][i_chan] = new TH1D(char_tmp,char_tmp,4096,0,4096);
                h_ADC_hittag0[i_layer][i_chip][i_chan]->SetDirectory(0);
                h_ADC_hittag1[i_layer][i_chip][i_chan]->SetDirectory(0);
            }
        }
    }
    std::cout << "Start Looping over events" << std::endl;
    TH2D *h2_trigger_layer_hit = new TH2D("h2_trigger_layer_hit","h2_trigger_layer_hit",5,-0.5,4.5,5,-0.5,4.5);
    int num_Loop = 0;
    double last_Event_Time = 0;
    for (int i = 0; i < tree_in->GetEntries(); ++i){
        Edep=0;
        BranchClear();
        if((i%1000)==0)cout<<i<<" out of "<<tree_in->GetEntries()<<endl;
        tree_in->GetEntry(i);
        _Event_No=_triggerID;
        if (_Event_Time < last_Event_Time) {
            num_Loop++;
            cout<<"Event time Loop detected"<<endl;
            _Event_Time = _Event_Time + num_Loop * (pow(2,30));
        }  
        _Detector_ID=1;
        int m = 0;
        int trigger_layer_hit[Layer_No]={0};
        for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
            trigger_layer_hit[i_layer]=0;
        }
        for (int i_hit = 0; i_hit < cellID->size(); ++i_hit){
            decode_cellid(cellID->at(i_hit),layer,chip,channel);
            if((hitTag->at(i_hit))==0) h_ADC_hittag0[layer][chip][channel]->Fill(HG_Charge->at(i_hit));
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
            _Hit_Z.push_back(z_layer_cosmic(layer));
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
        h2_trigger_layer_hit->Fill(trigger_layer_hit[8],trigger_layer_hit[32]);
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
    // TH3D *h3_sum0 = new TH3D("h3_sum0","h3_sum0",Layer_No,0,Layer_No,chip_No,0,chip_No,channel_No,0,channel_No);
    // TH3D *h3_sum1 = new TH3D("h3_sum1","h3_sum1",Layer_No,0,Layer_No,chip_No,0,chip_No,channel_No,0,channel_No);
    // for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
    //     fout->mkdir(Form("Layer_%d",i_layer));
    //     fout->cd(Form("Layer_%d",i_layer));
    //     for (int i_chip = 0; i_chip < chip_No; ++i_chip){
    //         fout->mkdir(Form("Layer_%d/Chip_%d",i_layer,i_chip));
    //         fout->cd(Form("Layer_%d/Chip_%d",i_layer,i_chip));
    //         for (int i_chan = 0; i_chan < channel_No; ++i_chan){
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->Write();
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->Write();
    //             TCanvas *c1 = new TCanvas(Form("c1_%d_%d_%d",i_layer,i_chip,i_chan),Form("c1_%d_%d_%d",i_layer,i_chip,i_chan),800,1800);
    //             c1->Divide(1,3);
    //             c1->cd(1);
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 0, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
    //             double minX_0 = GetMinXWithContent(h_ADC_hittag0[i_layer][i_chip][i_chan]);
    //             double maxX_0 = GetMaxXWithContent(h_ADC_hittag0[i_layer][i_chip][i_chan]);
    //             double minX_1 = GetMinXWithContent(h_ADC_hittag1[i_layer][i_chip][i_chan]);
    //             double maxX_1 = GetMaxXWithContent(h_ADC_hittag1[i_layer][i_chip][i_chan]);
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(min(minX_0,minX_1)-20,max(maxX_0,maxX_1)+20);
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(min(minX_0,minX_1)-20,max(maxX_0,maxX_1)+20);
    //             if (maxX_0 > minX_1){
    //                 std::cout << "threshold error: " << i_layer << " " << i_chip << " " << i_chan << std::endl;
    //                 int sum0 = h_ADC_hittag0[i_layer][i_chip][i_chan]->Integral(minX_1,maxX_0);
    //                 int sum1 = h_ADC_hittag1[i_layer][i_chip][i_chan]->Integral(minX_1,maxX_0);
    //                 int sum_all0 = h_ADC_hittag0[i_layer][i_chip][i_chan]->Integral(minX_0,maxX_0);
    //                 int sum_all1 = h_ADC_hittag1[i_layer][i_chip][i_chan]->Integral(minX_1,maxX_1);
    //                 std::cout << "sum0/sum_all0: " << sum0 << " " << sum_all0 << std::endl;
    //                 std::cout << "sum1/sum_all1: " << sum1 << " " << sum_all1 << std::endl;
    //                 h3_sum0->SetBinContent(i_layer+1,i_chip+1,i_chan+1, double(sum0)/double(sum_all0));
    //                 h3_sum1->SetBinContent(i_layer+1,i_chip+1,i_chan+1, double(sum1)/double(sum_all1));
    //             }
    //             TLine* h_ped_line = new TLine(ped_time[layer][chip][channel],0,ped_time[layer][chip][channel],h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximum());
    //             TLine* h_mip_line = new TLine(MIP[layer][chip][channel]+ped_time[layer][chip][channel],0,MIP[layer][chip][channel]+ped_time[layer][chip][channel],h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximum());
    //             h_ped_line->SetLineColor(kBlack);
    //             h_ped_line->SetLineStyle(2);
    //             h_ped_line->SetLineWidth(2);
    //             h_mip_line->SetLineColor(kGreen);
    //             h_mip_line->SetLineStyle(2);
    //             h_mip_line->SetLineWidth(2);
    //             // h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->GetXmin()-100,h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->GetXmax()+100);
    //             // h_ADC_hittag0[i_layer][i_chip][i_chan]->SetBins(h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->GetXmax()- h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->GetXmin() +200,h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->GetXmin()-100,h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->GetXmax()+100);
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetTitle("ADC");
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->GetYaxis()->SetTitle("Counts");
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->SetLineColor(kRed);
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->Draw();
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 1, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->SetTitle("ADC");
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->GetYaxis()->SetTitle("Counts");
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->SetLineColor(kBlue);
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->Draw("same");
    //             h_ped_line->Draw("same");
    //             h_mip_line->Draw("same");
    //             TLegend *leg = new TLegend(0.6,0.7,0.9,0.9);
    //             leg->AddEntry(h_ADC_hittag0[i_layer][i_chip][i_chan],"HitTag = 0","l");
    //             leg->AddEntry(h_ADC_hittag1[i_layer][i_chip][i_chan],"HitTag = 1","l");
    //             leg->SetBorderSize(0);
    //             leg->SetFillColor(0);
    //             leg->SetTextSize(0.03);
    //             leg->Draw();
    //             c1->Update();
    //             c1->Modified();
    //             // h_ADC_hittag0[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(minX_0-20,maxX_0+20);
    //             // h_ADC_hittag1[i_layer][i_chip][i_chan]->GetXaxis()->SetRangeUser(minX_1-20,maxX_1+20);
    //             c1->cd(2);
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 0, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
    //             h_ADC_hittag0[i_layer][i_chip][i_chan]->Draw("hist");
    //             c1->cd(3);
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->SetTitle(Form("HitTag = 1, Layer %d Chip %d Channel %d",i_layer,i_chip,i_chan));
    //             h_ADC_hittag1[i_layer][i_chip][i_chan]->Draw("hist");
    //             c1->Update();
    //             c1->Modified();
    //             c1->Write();
    //             // mkdir
    //             if (gSystem->AccessPathName(Form("Layer_%d/Chip_%d",i_layer,i_chip)))
    //             {
    //                 gSystem->mkdir(Form("Layer_%d/Chip_%d",i_layer,i_chip),true);
    //             }
    //             c1->SaveAs(Form("Layer_%d/Chip_%d/hittag_%d_%d_%d.png",i_layer,i_chip,i_layer,i_chip,i_chan));
    //             c1->Write();
    //         }
        // }
    // }

    // h3_sum0->Write();
    // h3_sum1->Write();
    // h3_sum0->SaveAs("h3_sum0.root");
    // h3_sum1->SaveAs("h3_sum1.root");
    // h2_trigger_layer_hit->Write();
    // h2_trigger_layer_hit->SaveAs("h2_trigger_layer_hit.root");
    // TCanvas *c2 = new TCanvas("c2","c2",800,600);
    // h2_trigger_layer_hit->SetTitle("Trigger Layer Hit");
    // h2_trigger_layer_hit->GetXaxis()->SetTitle("# of Hit in Layer 9");
    // h2_trigger_layer_hit->GetYaxis()->SetTitle("# of Hit in Layer 33");
    // h2_trigger_layer_hit->GetZaxis()->SetTitle("Counts");
    // h2_trigger_layer_hit->SetStats(0);
    // h2_trigger_layer_hit->Draw("COLZ");
    // c2->SetLogz();
    // c2->SaveAs("h2_trigger_layer_hit.png");
    // // h2_trigger_layer_hit->SaveAs("h2_trigger_layer_hit.png");
    // pedestal finding 
    double ped_new[Layer_No][chip_No][channel_No];
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            for (int i_chan = 0; i_chan < channel_No; ++i_chan){
                ped_new[i_layer][i_chip][i_chan] = h_ADC_hittag0[i_layer][i_chip][i_chan]->GetBinCenter(h_ADC_hittag0[i_layer][i_chip][i_chan]->GetMaximumBin());
            }
        }
    }
    // require the 0.8 MIP signal exist on the trigger layer
    std::vector<int> MuonCandidate;
    // std::vector<double> zx_chi2;
    // std::vector<double> zy_chi2;
    TFile *fout2 = new TFile("MuonCandidate2.root","RECREATE");
    int max_triggerID = 0;
    TH1D *h_triggerID = new TH1D("h_triggerID","h_triggerID",1e9,0,1e9);
    tree_in->Draw("TriggerID>>h_triggerID");
    max_triggerID = GetMaxXWithContent(h_triggerID);
    TH1D *h_time = new TH1D("h_time","h_time",1e9,0,1e9);
    tree_in->Draw("Event_Time>>h_time");
    int max_time =140;
    cout<<"max_time = "<<max_time<<endl;
    TH1D *h_time_full = new TH1D("h_time_full","h_time_full;Event_Time",20,0, max_time+1);
    TH1D *h_time_MuonCandidate = new TH1D("h_time_MuonCandidate","h_time_MuonCandidate;Event_Time",20,0, max_time+1);
    TH1D *h_triggerID_full = new TH1D("h_triggerID_full","h_triggerID_full;trigger_ID",20,0, max_triggerID+1);
    TH1D *h_triggerID_MuonCandidate = new TH1D("h_triggerID_MuonCandidate","h_triggerID_MuonCandidate;trigger_ID",20,0, max_triggerID+1);
    max_triggerID = GetMaxXWithContent(h_triggerID);
    cout<<"max_triggerID = "<<max_triggerID<<endl;
    TCanvas *c2 = new TCanvas("c2","c2",800,600);
    c2->SaveAs("MuonCandidate2.pdf(");
    TH1D *h_chi2perndf_x = new TH1D("h_chi2perndf_x","chi2/ndf of xz plane;chi2/ndf",200,0,50);
    TH1D *h_nHits = new TH1D("h_nHits_x","nHits;nHits",100,0,100);
    TH1D *h_slope_x = new TH1D("h_slope_x","slope of xz plane;tan#theta",50,-1,1);
    TH1D *h_intercept_x = new TH1D("h_intercept_x","intercept of xz plane;intercept",100,-500,500);
    TH1D *h_chi2perndf_y = new TH1D("h_chi2perndf_y","chi2/ndf of yz plane;chi2/ndf",200,0,50);
    TH1D *h_slope_y = new TH1D("h_slope_y","slope of yz plane;tan#theta",50,-1,1);
    TH1D *h_intercept_y = new TH1D("h_intercept_y","intercept of yz plane;intercept",100,-500,500);
    TH1D *h_nHits_full = new TH1D("h_nHits_xy","nHits ;nHits",100,0,100);
    std::cout << "Start Looping over events" << std::endl;
    for (int i = 0; i < tree_in->GetEntries(); ++i){
    // for (int i = 0; i < 10000; ++i){
        // Edep=0;
        // BranchClear();
        if((i%1000)==0)cout<<i<<" out of "<<tree_in->GetEntries()<<endl;
        tree_in->GetEntry(i);
        // _Event_No=_triggerID;
        // _Detector_ID=1;
        int m = 0;
        int trigger0_MIP_exist = 0;
        std::pair<double,double> trigger0_xy;
        int trigger1_MIP_exist = 0;
        std::pair<double,double> trigger1_xy;
        int nhits = 0;
        for (int i_hit = 0; i_hit < cellID->size(); ++i_hit){
            decode_cellid(cellID->at(i_hit),layer,chip,channel);
            // if((hitTag->at(i_hit))==0) h_ADC_hittag0[layer][chip][channel]->Fill(HG_Charge->at(i_hit));
            // else h_ADC_hittag1[layer][chip][channel]->Fill(HG_Charge->at(i_hit));
            // if((hitTag->at(i_hit))==0) continue;
            // _cellID.push_back(cellID->at(i_hit));
            if (HG_Charge->at(i_hit) > ped_new[layer][chip][channel] + 0.5 * MIP[layer][chip][channel]){
                if (!ExcludeCh(layer,chip,channel)){
                    nhits++;
                }
            }
            if (layer == 8){
                if (HG_Charge->at(i_hit) > ped_new[layer][chip][channel] + 0.5 * MIP[layer][chip][channel]){
                    // hitE=( HG_Charge->at(i_hit) - ped_new[layer][chip][channel] )*MIP_E/MIP[layer][chip][channel];
                    trigger0_MIP_exist++;
                    trigger0_xy = std::make_pair(Pos_X(channel,chip),Pos_Y(channel,chip));
                }   
            }else if (layer == 32){
                if (HG_Charge->at(i_hit) > ped_new[layer][chip][channel] + 0.5 * MIP[layer][chip][channel]){
                    // hitE=( HG_Charge->at(i_hit) - ped_new[layer][chip][channel] )*MIP_E/MIP[layer][chip][channel];
                    trigger1_MIP_exist++;
                    trigger1_xy = std::make_pair(Pos_X(channel,chip),Pos_Y(channel,chip));
                }   
            }else{
                continue;
            }
        }
        h_nHits_full->Fill(nhits);
        h_triggerID_full->Fill(_triggerID);
        h_time_full->Fill(_Event_Time);
        nhits = 0;
        if ((trigger0_MIP_exist > 0 && trigger1_MIP_exist > 0)||(trigger0_MIP_exist > 0 && trigger1_MIP_exist == 0 )){
            cout << "Event No: " << i << endl;
            cout << "trigger0_MIP_exist: " << trigger0_MIP_exist << " trigger1_MIP_exist: " << trigger1_MIP_exist << endl;
            cout << "trigger0_xy: " << trigger0_xy.first << " " << trigger0_xy.second << endl;
            cout << "trigger1_xy: " << trigger1_xy.first << " " << trigger1_xy.second << endl;
            MuonCandidate.push_back(i);
            // TH3D* h_display=new TH3D("display","display",534,0,1602,18,-360,360,18,-360,360);
	        // // h_display->GetXaxis()->SetRangeUser(0,800);
        	// TCanvas *c = new TCanvas("c", "c",48,130,1000,723);
            // c->cd();
	        // // gStyle->SetOptStat(0);
            // c->SetRightMargin(0.15);
            // c->SetLeftMargin(0.15);
            // c->SetBottomMargin(0.15);
            // c->SetTopMargin(0.15);
            // h_display->GetXaxis()->SetTitle("Z [mm]");
            // h_display->GetYaxis()->SetTitle("X [mm]");
            // h_display->GetZaxis()->SetTitle("Y [mm]");
            // h_display->GetXaxis()->SetTitleOffset(1.2);
            // h_display->GetYaxis()->SetTitleOffset(1.2);
            // h_display->GetZaxis()->SetTitleOffset(1.2);
            // h_display->GetXaxis()->SetTitleSize(0.05);
            // h_display->GetYaxis()->SetTitleSize(0.05);
            // h_display->GetZaxis()->SetTitleSize(0.05);
            for (int i_hit = 0; i_hit < cellID->size(); ++i_hit){
                decode_cellid(cellID->at(i_hit),layer,chip,channel);
                double hitE=0;
                if (ExcludeCh(layer,chip,channel)) continue;
                if( (HG_Charge->at(i_hit))-ped_new[layer][chip][channel] < gain_plat[layer][chip][channel]-SwitchPoint )
                {
                    hitE=( HG_Charge->at(i_hit) -ped_new[layer][chip][channel] )*MIP_E/MIP[layer][chip][channel];
                }else{
                    hitE=( LG_Charge->at(i_hit) - ped_charge[layer][chip][channel] )*gain_ratio[layer][chip][channel]*MIP_E/MIP[layer][chip][channel];
                } 
                if(hitE > 0.5 * MIP_E){
                    // h_display->Fill(z_layer_cosmic(layer),Pos_X(channel,chip),Pos_Y(channel,chip),hitE);
                    nhits++;
                }
            }
            if (nhits != 40 && trigger0_MIP_exist > 0 && trigger1_MIP_exist == 0){
                continue;
            }
            // h_display->SetTitle(Form("Event %d",i));
            // h_display->GetZaxis()->SetRangeUser(0,1000);
            // h_display->Draw("box2");
            // h_display->Write(Form("display_%d",i));
            TCanvas *c_2D = new TCanvas("c_2D", "c_2D", 48, 130, 1000, 723);
            c_2D->Divide(1,2);
            // c_2D->cd(1);
            c_2D->cd(1)->SetRightMargin(0.3);
            // gStyle->SetOptStat(0);
            TH2D *h2_display_zx=new TH2D("display_zy","display_zy",534,0,1602,18,-360,360);
            // h2_display_zx->GetXaxis()->SetRangeUser(0,800);
            h2_display_zx->GetXaxis()->SetTitle("Z [mm]");
            h2_display_zx->GetYaxis()->SetTitle("X [mm]");
            // h2_display_zx->GetXaxis()->SetTitleOffset(1.2);
            // h2_display_zx->GetYaxis()->SetTitleOffset(1.2);
            h2_display_zx->GetXaxis()->SetTitleSize(0.05);
            h2_display_zx->GetYaxis()->SetTitleSize(0.05);
            for (int i_hit = 0; i_hit < cellID->size(); ++i_hit){
                decode_cellid(cellID->at(i_hit),layer,chip,channel);
                double hitE=0;
                if (ExcludeCh(layer,chip,channel)) continue;
                if( (HG_Charge->at(i_hit))-ped_new[layer][chip][channel] < gain_plat[layer][chip][channel]-SwitchPoint )
                {
                    hitE=( HG_Charge->at(i_hit) -ped_new[layer][chip][channel] )*MIP_E/MIP[layer][chip][channel];
                }else{
                    hitE=( LG_Charge->at(i_hit) - ped_charge[layer][chip][channel] )*gain_ratio[layer][chip][channel]*MIP_E/MIP[layer][chip][channel];
                } 
                if(hitE > 0.5 * MIP_E) h2_display_zx->Fill(z_layer_cosmic(layer),Pos_X(channel,chip),hitE);
            }
            h2_display_zx->SetTitle(Form("Event %d",i));
            // h2_display_zx->GetYaxis()->SetRangeUser(0,1000);
            // h2_display_zx->Draw("colz");
            std::tuple <double,double,double, int> fit_result = FitMuonTrack(h2_display_zx);
            h_chi2perndf_x->Fill(std::get<2>(fit_result));
            h_nHits->Fill(nhits);
            h_slope_x->Fill(std::get<0>(fit_result));
            h_intercept_x->Fill(std::get<1>(fit_result));

            // FitMuonTrack(h2_display_zx);
            // c2->SaveAs(Form("MuonCandidate.pdf",i));
            // c_2D->cd(2);
            c_2D->cd(2)->SetRightMargin(0.3);
            TH2D *h2_display_zy=new TH2D("display_zy","display_zy",534,0,1602,18,-360,360);
            // h2_display_zy->GetXaxis()->SetRangeUser(0,800);
            h2_display_zy->GetXaxis()->SetTitle("Z [mm]");
            h2_display_zy->GetYaxis()->SetTitle("Y [mm]");
            // h2_display_zy->GetXaxis()->SetTitleOffset(1.2);
            // h2_display_zy->GetYaxis()->SetTitleOffset(1.2);
            h2_display_zy->GetXaxis()->SetTitleSize(0.05);
            h2_display_zy->GetYaxis()->SetTitleSize(0.05);
            for (int i_hit = 0; i_hit < cellID->size(); ++i_hit){
                decode_cellid(cellID->at(i_hit),layer,chip,channel);
                double hitE=0;
                if (ExcludeCh(layer,chip,channel)) continue;
                if( (HG_Charge->at(i_hit))-ped_new[layer][chip][channel] < gain_plat[layer][chip][channel]-SwitchPoint )
                {   
                    hitE=( HG_Charge->at(i_hit) -ped_new[layer][chip][channel] )*MIP_E/MIP[layer][chip][channel];
                }else{
                    hitE=( LG_Charge->at(i_hit) - ped_charge[layer][chip][channel] )*gain_ratio[layer][chip][channel]*MIP_E/MIP[layer][chip][channel];
                } 
                if(hitE > 0.5 * MIP_E) h2_display_zy->Fill(z_layer_cosmic(layer),Pos_Y(channel,chip),hitE);
            }
            h2_display_zy->SetTitle(Form("Event %d",i));
            // h2_display_zy->GetYaxis()->SetRangeUser(0,1000);
            // h2_display_zy->Draw("colz");
            // FitMuonTrack(h2_display_zy);
            std::tuple <double,double,double, int> fit_result2 = FitMuonTrack(h2_display_zy);
            h_chi2perndf_y->Fill(std::get<2>(fit_result2));
            // h_nHits_y->Fill(std::get<3>(fit_result2));
            h_slope_y->Fill(std::get<0>(fit_result2));
            h_intercept_y->Fill(std::get<1>(fit_result2));
            h_triggerID_MuonCandidate->Fill(_triggerID);
            h_time_MuonCandidate->Fill(_Event_Time);
            // c_2D->SaveAs("MuonCandidate2.pdf");
            // c_2D->SaveAs(Form("MuonCandidate_%d.png",i));
        }
    }
    c2->SaveAs("MuonCandidate2.pdf)");
    fout2->cd();
    // for (int i = 0; i < MuonCandidate.size(); ++i){
    //     cout << "MuonCandidate: " << MuonCandidate[i] << endl;
    // }
    TCanvas *c3 = new TCanvas("c3","c3",800,600);
    h_chi2perndf_x->SetLineColor(kRed);
    h_chi2perndf_x->Scale(1./h_chi2perndf_x->Integral());
    h_chi2perndf_x->SetLineWidth(2);
    h_chi2perndf_x->GetYaxis()->SetTitle("Normalized Counts");
    h_chi2perndf_y->SetLineColor(kBlue);
    h_chi2perndf_y->Scale(1./h_chi2perndf_y->Integral());
    h_chi2perndf_y->SetLineWidth(2);
    h_chi2perndf_y->Draw("hist");
    h_chi2perndf_x->Draw("hist same");
    TLegend *leg = new TLegend(0.6,0.7,0.9,0.9);
    leg->AddEntry(h_chi2perndf_x,"xz plane","l");
    leg->AddEntry(h_chi2perndf_y,"yz plane","l");
    leg->SetBorderSize(0);
    leg->SetFillColor(0);
    leg->Draw();
    c3->SaveAs("MuonCandidate2_chi2.png");
    c3->SetLogy();
    h_nHits_full->SetLineColor(kRed);
    h_nHits_full->SetLineWidth(2);
    h_nHits->SetLineColor(kBlue);
    h_nHits->SetLineWidth(2);
    h_nHits_full->Draw("hist");
    h_nHits->Draw("hist same");
    h_nHits_full->GetXaxis()->SetTitle("nHits");
    h_nHits_full->GetYaxis()->SetTitle("Counts");
    TLatex *latex = new TLatex();
    latex->SetTextSize(0.03);
    // latex->SetTextColor(kRed);
    latex->SetTextFont(42);
    latex->DrawLatexNDC(0.2, 0.85, Form("Run %d", _Run_No));
    // latex->DrawLatexNDC(0.75, 0.6, Form("Time %s", 
    latex->DrawLatexNDC(0.2, 0.8, Form("Full Data %d Events" , tree_in->GetEntries()));
    latex->DrawLatexNDC(0.2, 0.75, Form("MuonCandidate %d Events" , MuonCandidate.size()));
    TLegend *leg2 = new TLegend(0.6,0.7,0.85,0.85);
    leg2->AddEntry(h_nHits_full,"full data","l");
    leg2->AddEntry(h_nHits,"MuonCandidate","l");
    leg2->SetBorderSize(0);
    leg2->SetFillColor(0);
    leg2->Draw();
    c3->SaveAs("MuonCandidate2_nHits.png");
    TEfficiency *efficiency = new TEfficiency(*h_triggerID_MuonCandidate, *h_triggerID_full);
    TCanvas *c_eff = new TCanvas("c_eff","c_eff",800,600);
    efficiency->SetTitle("MuonCandidate Efficiency; Trigger ID; Efficiency");
    // efficiency->SetLineColor(kRed);
    efficiency->Draw();
    c_eff->SaveAs("MuonCandidate2_efficiency.png");
    TCanvas *c4 = new TCanvas("c4","c4",800,600);
    c4->Divide(2,1);
    c4->cd(1);
    h_triggerID_full->SetLineColor(kRed);
    h_triggerID_full->SetLineWidth(2);
    h_triggerID_full->GetXaxis()->SetTitle("Trigger ID");
    h_triggerID_full->GetYaxis()->SetTitle("Counts");
    h_triggerID_full->Draw("hist");
    c4->cd(2);
    h_triggerID_MuonCandidate->SetLineColor(kBlue);
    h_triggerID_MuonCandidate->SetLineWidth(2);
    h_triggerID_MuonCandidate->GetXaxis()->SetTitle("Trigger ID");
    h_triggerID_MuonCandidate->GetYaxis()->SetTitle("Counts");
    h_triggerID_MuonCandidate->Draw("hist");
    c4->SaveAs("MuonCandidate2_triggerID.png");
    TCanvas *c5 = new TCanvas("c5","c5",800,1500);
    c5->Divide(1,3);
    c5->cd(1);
    TLatex *latex2 = new TLatex();
    latex2->SetTextSize(0.03);
    latex2->SetTextFont(42);
    latex2->DrawLatexNDC(0.2, 0.85, Form("Run %d", _Run_No));
    latex2->DrawLatexNDC(0.2, 0.8, Form("Full Data %d Events" , tree_in->GetEntries()));
    latex2->DrawLatexNDC(0.2, 0.75, Form("MuonCandidate %d Events" , MuonCandidate.size()));
    h_time_full->SetLineColor(kRed);
    h_time_full->SetLineWidth(2);
    h_time_full->GetXaxis()->SetTitle("Event Time [s]");
    h_time_full->GetYaxis()->SetTitle("Hz");
    h_time_full->SetTitle("Full Data Event Time Distribution");
    h_time_full->Scale(1./(h_time_full->GetXaxis()->GetXmax()/h_time_full->GetNbinsX())); // Scale to Hz
    h_time_full->Draw("hist");
    c5->cd(2);
    h_time_MuonCandidate->SetLineColor(kBlue);
    h_time_MuonCandidate->SetLineWidth(2);
    h_time_MuonCandidate->GetXaxis()->SetTitle("Event Time [s]");
    h_time_MuonCandidate->GetYaxis()->SetTitle("Hz");
    h_time_MuonCandidate->SetTitle("MuonCandidate Event Time Distribution");
    h_time_MuonCandidate->Scale(1./(h_time_MuonCandidate->GetXaxis()->GetXmax()/h_time_MuonCandidate->GetNbinsX())); // Scale to Hz
    h_time_MuonCandidate->Draw("hist");
    c5->cd(3);
    TEfficiency *efficiency2 = new TEfficiency(*h_time_MuonCandidate, *h_time_full);
    // TCanvas *c_eff2 = new TCanvas("c_eff2","c_eff2",800,600);
    efficiency2->SetTitle("MuonCandidate Efficiency; Event Time [s]; Efficiency");
    // efficiency2->SetLineColor(kRed);
    efficiency2->Draw();
    c5->SaveAs("MuonCandidate2_time.png");
    // c_eff2->SaveAs("MuonCandidate2_time_efficiency.png");
    efficiency2->Write();
    h_chi2perndf_x->Write();
    h_slope_x->Write();
    h_intercept_x->Write();
    h_chi2perndf_y->Write();
    h_slope_y->Write();
    h_intercept_y->Write();
    fout2->Close();           
    fout->Close();
    return 1;
}
