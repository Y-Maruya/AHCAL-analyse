#include "RawtoRoot.h"
#include "Global.h"
#include "langaus.h"
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
#include <unordered_map>
#include <thread>
#include <mutex>
using namespace std;
int main(int argc,char *argv[]){
    double start = clock();
    raw2Root tw;
    tw.MIPlist(argv[1]);
    double end = clock();
    cout<<"end of mip : Time : "<<(end-start)/CLOCKS_PER_SEC<<endl;
    return 0;
}
int raw2Root::MIPlist(const string _list){
    ReadList(_list);
    TFile *fin,*fout;
    TTree *tin,*tout;
    fout=TFile::Open(TString(_list)+"_mip.root","recreate");
    unordered_map<int, TH1D*> mmip;
    for(int layer=0;layer<40;layer++){
        TString slayer="layer"+TString(to_string(layer).c_str());
        for(int chip=0;chip<9;chip++){
            TString schip="chip"+TString(to_string(chip).c_str());
            for(int channel=0;channel<36;channel++){
                TString schannel="channel"+TString(to_string(channel).c_str());
                TString name ="MIP Spectrum "+slayer+" "+schip+" "+schannel;
                int cellid=layer*1e5+chip*1e4+channel;
                mmip[cellid]=new TH1D(name,name,128,-1000,3096);
            }
        }
    }
    tout=new TTree("mip","mip");
    // TH2I *hitmap = new TH2I("hitmap", "hitmap", 18, -360, 360, 18, -360, 360);
    double MPV=0,width=0,gaus_sigma=0,max_x=0,FWHM=0,
           chi2=0,ndf=0,chi2perndf=0;
    double _MPV[40][9][36],_width[40][9][36],_gaus_sigma[40][9][36],_max_x[40][9][36],_FWHM[40][9][36],_chi2[40][9][36],_ndf[40][9][36],_chi2perndf[40][9][36];
    std::fill(_MPV[0][0],_MPV[0][0]+12960,0);
    std::fill(_width[0][0],_width[0][0]+12960,0);
    std::fill(_max_x[0][0],_max_x[0][0]+12960,0);
    std::fill(_FWHM[0][0],_FWHM[0][0]+12960,0);
    std::fill(_gaus_sigma[0][0],_gaus_sigma[0][0]+12960,0);
    std::fill(_chi2[0][0],_chi2[0][0]+12960,0);
    std::fill(_ndf[0][0],_ndf[0][0]+12960,0);
    std::fill(_chi2perndf[0][0],_chi2perndf[0][0]+12960,0);
    int cellid=0,entries=0;
    tout->Branch("MPV",&MPV);
    tout->Branch("width",&width);
    tout->Branch("gaus_sigma",&gaus_sigma);
    tout->Branch("CellID",&cellid);
    tout->Branch("entries",&entries);
    tout->Branch("max_x",&max_x);
    tout->Branch("FWHM",&FWHM);
    tout->Branch("chi2",&chi2);
    tout->Branch("ndf",&ndf);
    tout->Branch("chi2perndf",&chi2perndf);
    for_each(list.begin(),list.end(),[&](string tmp){
        cout<<"Reading: "<<tmp<<endl;
        fin=TFile::Open(TString(tmp),"read");
        // tin=(TTree*)fin->Get("EventTree");
        // ReadCalibTree(tin);
        for (int layer = 0; layer < 40; layer++) {
            for (int chip = 0; chip < 9; chip++) {
                for (int channel = 0; channel < 36; channel++) {
                    cellid = layer * 1e5 + chip * 1e4 + channel;
                    // mmip[cellid]->Reset();
                    std::unique_ptr<TH1D> h_ADC((TH1D*)fin->Get("Layer_"+TString(to_string(layer).c_str())+"/Chip_"+TString(to_string(chip).c_str())+"/h_ADC_MuonTrack_"+TString(to_string(layer).c_str())+"_"+TString(to_string(chip).c_str())+"_"+TString(to_string(channel).c_str())));
                    // (TH1D*)fin->Get("Layer"+TString(to_string(layer).c_str())+"/Chip"+TString(to_string(chip).c_str())+"/h_ADC_MuonTrack_"+TString(to_string(layer).c_str())+"_"+TString(to_string(chip).c_str())+"_"+TString(to_string(channel).c_str()));
                    if (!h_ADC) {
                        cout << "Warning: h_ADC_MuonTrack not found for layer " << layer << " chip " << chip << " channel " << channel << endl;
                        continue;
                    }
                    mmip[cellid]->Add(h_ADC.get());
                    // mmip[cellid]->Add((TH1D*)fin->Get("Layer"+TString(to_string(layer).c_str())+"/Chip"+TString(to_string(chip).c_str())+"/h_ADC_MuonTrack_"+TString(to_string(layer).c_str())+"_"+TString(to_string(chip).c_str())+"_"+TString(to_string(channel).c_str())));
                    entries = mmip[cellid]->GetEntries();
                }
            }
        }
        fin->Close();
    });

    mutex g_mutex;
    auto ffit=[&](int layer){
        double fr[2];
        double sv[4], pllo[4], plhi[4], fps[4], fpe[4];
        double chisqr;
        int ndf;
        printf("fitting layer %d ...\n",layer);
        for(int chip=0;chip<9;chip++){
            for(int channel=0;channel<36;channel++){
                int cellid=layer*1e5+chip*1e4+channel;
                int entries=mmip[cellid]->GetEntries();
                if(entries<100){
                    // tout->Fill();
                    // mmip[cellid]->Write();
                    continue;
                }
                fr[0] = 00;
                fr[1] = 1200;
                sv[0] = 40;
                sv[1] = 344;
                sv[2] = mmip[cellid]->Integral(0,3096);
                sv[3] = 80;
                pllo[0] = 10;
                pllo[1] = 100;
                pllo[2] = sv[2] / 12;
                pllo[3] = 10;
                plhi[0] = 150;
                plhi[1] = 700;
                plhi[2] = sv[2] * 100;
                plhi[3] = 200;
        // g_mutex.lock();
                langaufit(mmip[cellid], fr, sv, pllo, plhi, fps, fpe, &chisqr, &ndf);
        // g_mutex.unlock();
                double maxx=0,fwhm;
                langaupro(fps,maxx,fwhm);
                _max_x[layer][chip][channel]=maxx;
                _FWHM[layer][chip][channel]=fwhm;
                _MPV[layer][chip][channel]=fps[1];
                _width[layer][chip][channel]=fps[0];
                _gaus_sigma[layer][chip][channel]=fps[3];
                _chi2[layer][chip][channel]=chisqr;
                _ndf[layer][chip][channel]=ndf;
                if(ndf>0){
                    _chi2perndf[layer][chip][channel]=chisqr/ndf;
                } else {
                    _chi2perndf[layer][chip][channel]=0;
                }
            }
        }
        printf("fitted layer %d\n",layer);
    };
    for(int i = 0; i < 40; i++){
        ffit(i);
    }
        // thread th[40];
        // for(int i=0;i<40;i++){
        //     th[i]=thread(ffit,i);
        // }
        // for(int i=0;i<40;i++){
        //     th[i].join();
        // }
    fout->cd();
    // hitmap->Write();
    TString dir="histogram";
    fout->mkdir(dir);
    for(int layer=0;layer<40;layer++){
        TString slayer="layer"+TString(to_string(layer).c_str());
        fout->mkdir(dir+"/"+slayer);
        for(int chip=0;chip<9;chip++){
            TString schip="chip"+TString(to_string(chip).c_str());
            fout->mkdir(dir+"/"+slayer+"/"+schip);
            fout->cd(dir+"/"+slayer+"/"+schip);
            for(int channel=0;channel<36;channel++){
                
                cellid=layer*1e5+chip*1e4+channel;
                entries=mmip[cellid]->GetEntries();
                if(entries<100){
                    tout->Fill();
                    mmip[cellid]->Write();
                    continue;
                }
                mmip[cellid]->Write();
                MPV=_MPV[layer][chip][channel];
                width=_width[layer][chip][channel];
                gaus_sigma=_gaus_sigma[layer][chip][channel];
                max_x=_max_x[layer][chip][channel];
                FWHM=_FWHM[layer][chip][channel];
                chi2=_chi2[layer][chip][channel];
                ndf=_ndf[layer][chip][channel];
                chi2perndf=_chi2perndf[layer][chip][channel];
                tout->Fill();
            }
        }
    }
    fout->cd();
    tout->Write();
    fout->Close();
    return 1;
}

int raw2Root::MIP(vector<int> *_cellid,vector<double> *Hit_E){
    int layerlen[40]={0};
    for(int i=0;i<_cellid->size();i++){
        int layer=_cellid->at(i)/100000;
        layerlen[layer]++;
    }
    for(int i=0;i<40;i++){
        if(layerlen[i]>2){
            return 0;
        }
    }
    return 1;
}