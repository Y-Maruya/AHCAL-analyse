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
#include "TGraphAsymmErrors.h"
#include "TGraph.h"
#include "TGaxis.h"
#include "TH3D.h"
#include "TEfficiency.h"
// #include </afs/ihep.ac.cn/users/s/shiyk/YukunToolBox/Root.h>
//#include "Event.h"
int layer,chip,channel;
using namespace std;
char char_tmp[200];
std::string saveornot = "";
double z_layer_cosmic(int layer) {
    return (layer/2) * 80.0 + (layer % 2) * 20.0; 
} 
// MC 
class MCTrack {
    public:
        MCTrack(double* x_offset, double* y_offset) {
            for (int i = 0; i < 40; ++i) {
                x_offset_[i] = x_offset[i];
                y_offset_[i] = y_offset[i];
            }
            // Remove TTree creation from constructor - will be created later when TFile is open
            out_tree = nullptr;
            random_gen = new TRandom();
        }
        
        void InitializeTree() {
            // Create tree after TFile is opened
            out_tree = new TTree("MCTrack", "MC Track Data");
            out_tree->Branch("x_offset", x_offset_, "x_offset[40]/D");
            out_tree->Branch("y_offset", y_offset_, "y_offset[40]/D");
            out_tree->Branch("trigger_layer0", &trigger_layer0_, "trigger_layer0/I");
            out_tree->Branch("trigger_layer1", &trigger_layer1_, "trigger_layer1/I");
            out_tree->Branch("x_trigger0", &x_trigger0_, "x_trigger0/D");
            out_tree->Branch("y_trigger0", &y_trigger0_, "y_trigger0/D");
            out_tree->Branch("x_trigger1", &x_trigger1_, "x_trigger1/D");
            out_tree->Branch("y_trigger1", &y_trigger1_, "y_trigger1/D");
            out_tree->Branch("cos_theta", &cos_theta_, "cos_theta/D");
            out_tree->Branch("phi", &phi_, "phi/D");
            out_tree->Branch("hit_position_x", hit_position_x_, "hit_position_x[40]/D");
            out_tree->Branch("hit_position_y", hit_position_y_, "hit_position_y[40]/D");
            out_tree->Branch("hit_layers", &_hit_layers);
            out_tree->Branch("hit_chips", &_hit_chips);
            out_tree->Branch("hit_channels", &_hit_channels);
        }
        ~MCTrack() {
            if (random_gen) {
                delete random_gen;
                random_gen = nullptr;
            }
        }
        void SetTriggerLayers(int trigger_layer0, int trigger_layer1) {
            trigger_layer0_ = trigger_layer0;
            trigger_layer1_ = trigger_layer1;
        }
        void GenerateTracks(int Nevents){
            TF1* f1 = new TF1("f1", "x^2", 0, 1);
            while (Nevents > 0) {
                Clear();
                x_trigger0_ = gRandom->Uniform(-HBU_X*1.5, HBU_X*1.5) - x_offset_[trigger_layer0_];
                y_trigger0_ = gRandom->Uniform(-HBU_Y*0.5, HBU_Y*0.5) - y_offset_[trigger_layer0_];
                cos_theta_ = f1->GetRandom();
                double tantheta_ = sqrt((1/cos_theta_/cos_theta_) - 1);
                phi_ = gRandom->Uniform(-3.14, 3.14);
                x_trigger1_ = x_trigger0_ + tantheta_ * cos(phi_) * abs(z_layer_cosmic(trigger_layer0_) - z_layer_cosmic(trigger_layer1_));
                y_trigger1_ = y_trigger0_ + tantheta_ * sin(phi_) * abs(z_layer_cosmic(trigger_layer0_) - z_layer_cosmic(trigger_layer1_));
                if (abs(x_trigger1_ + x_offset_[trigger_layer1_]) > HBU_X*1.5 || abs(y_trigger1_ + y_offset_[trigger_layer1_]) > HBU_Y*0.5) continue;
                for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
                    hit_position_x_[i_layer] = x_trigger0_ + (z_layer_cosmic(i_layer) - z_layer_cosmic(trigger_layer0_)) * tantheta_ * cos(phi_);
                    hit_position_y_[i_layer] = y_trigger0_ + (z_layer_cosmic(i_layer) - z_layer_cosmic(trigger_layer0_)) * tantheta_ * sin(phi_);
                    if (abs(hit_position_x_[i_layer] + x_offset_[i_layer]) > HBU_X*1.5 || abs(hit_position_y_[i_layer] + y_offset_[i_layer]) > HBU_Y*0.5) {
                        hit_position_x_[i_layer] = std::numeric_limits<double>::quiet_NaN(); // Set to NaN if out of bounds
                        hit_position_y_[i_layer] = std::numeric_limits<double>::quiet_NaN();
                        continue;
                    }
                    int chip = 0;
                    int channel = 0;
                    inverse(hit_position_x_[i_layer] + x_offset_[i_layer], hit_position_y_[i_layer] + y_offset_[i_layer], chip, channel);
                    if (chip < 0 || chip >= chip_No || channel < 0 || channel >= channel_No) {
                        hit_position_x_[i_layer] = std::numeric_limits<double>::quiet_NaN(); // Set to NaN if out of bounds
                        hit_position_y_[i_layer] = std::numeric_limits<double>::quiet_NaN();
                    }
                    _hits.push_back(std::make_tuple(i_layer, chip, channel));
                    _hit_layers.push_back(i_layer);
                    _hit_chips.push_back(chip);
                    _hit_channels.push_back(channel);
                }
                // _hits.push_back(std::make_tuple(i_layer, chip, channel));
                out_tree->Fill();
                Nevents--;
                if (Nevents % 1000 == 0) {
                    std::cout << "Generated " << Nevents << " events remaining." << std::endl;
                }
            }
            delete f1;
        }
        void Clear() {
            x_trigger0_ = 0;
            y_trigger0_ = 0;
            x_trigger1_ = 0;
            y_trigger1_ = 0;
            cos_theta_ = 0;
            phi_ = 0;
            for (int i = 0; i < 40; ++i) {
                hit_position_x_[i] = std::numeric_limits<double>::quiet_NaN();
                hit_position_y_[i] = std::numeric_limits<double>::quiet_NaN();
            }
            _hits.clear();
            _hit_layers.clear();
            _hit_chips.clear();
            _hit_channels.clear(); // Add this line to clear channels vector
        }
        std::vector<int> _hit_layers;
        std::vector<int> _hit_chips;
        std::vector<int> _hit_channels;
        
        TTree* out_tree;
    private:
        double x_offset_[40];
        double y_offset_[40];
        int trigger_layer0_;
        int trigger_layer1_;
        TRandom* random_gen;
        double x_trigger0_;
        double y_trigger0_;
        double y_trigger1_;
        double x_trigger1_;
        double cos_theta_;
        double phi_;
        double hit_position_x_[40];
        double hit_position_y_[40];
        std::vector<std::tuple<int, int, int>> _hits;
};

    
Int_t main(int argc,char *argv[])
{
    if (argc < 9) {
        cout << "Usage: " << argv[0] << " <dat_file> <ped_file> <dac_file> <MIP_file> <output_file> <trigger_layer0> <trigger_layer1> <offset_file> [save_option]" << endl;
        return 1;
    }
    
    double start = clock();
    raw2Root tw;
    int trigger_layer0 = std::stoi(argv[6]);
    int trigger_layer1 = std::stoi(argv[7]);
    string offset_file = argv[8];
    
    if (argc > 9) {
        saveornot = std::string(argv[9]);
        std::cout << "Save option: " << saveornot << std::endl;
    }
    
    // Load offsets from file
    double x_offset[40];
    double y_offset[40];
    
    // Initialize offsets to zero
    for (int i = 0; i < 40; ++i) {
        x_offset[i] = 0.0;
        y_offset[i] = 0.0;
    }
    
    // Load offsets from file
    TFile* offset_file_obj = TFile::Open(offset_file.c_str(), "READ");
    if (offset_file_obj) {
        TTree* offset_tree = (TTree*)offset_file_obj->Get("offset_values");
        if (offset_tree) {
            int layer_id;
            double x_offset_val, y_offset_val;
            
            offset_tree->SetBranchAddress("layer", &layer_id);
            offset_tree->SetBranchAddress("x_offset", &x_offset_val);
            offset_tree->SetBranchAddress("y_offset", &y_offset_val);
            
            for (int i = 0; i < offset_tree->GetEntries(); ++i) {
                offset_tree->GetEntry(i);
                if (layer_id >= 0 && layer_id < 40) {
                    x_offset[layer_id] = x_offset_val;
                    y_offset[layer_id] = y_offset_val;
                }
            }
            cout << "Successfully loaded offsets from " << offset_file << endl;
        } else {
            cout << "Warning: Could not find offset_values tree in " << offset_file << endl;
        }
        offset_file_obj->Close();
        delete offset_file_obj;
    } else {
        cout << "Warning: Could not open offset file " << offset_file << endl;
    }
    
    // Call the offset-corrected analysis
    tw.forMuon_MC(argv[1],argv[2],argv[3],argv[4],argv[5], trigger_layer0, trigger_layer1, x_offset, y_offset);
    
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
    // if (layer == 0 && chip == 0) return 1;
    // if (layer == 0 && chip == 1) return 1;
    // if (chip == 7 && channel == 35) return 1;
    return 0;
}

int inverse_z_layer_cosmic(double z) {
    if (z <= 0 || z >= 1600) {
        std::cout << "Error: z out of range: " << z << std::endl;
        return -1; // Error code for out of range
    }
    int layer_half = static_cast<int>(z / 80.0);
    int layer = layer_half * 2; // Even layers
    if (z >= 80.0 * layer_half + 20.0) {
        layer += 1; // Adjust for odd layers
    }
    if (layer < 0 || layer >= 40) {
        std::cout << "Error: layer out of range: " << layer << std::endl;
        return -1; // Error code for out of range
    }
    return layer;
}

TH1D* h_costheta2(int trigger0, int trigger1){
    TH1D* h_costheta = new TH1D("h_costheta2","h_costheta2",100,0,1);
    h_costheta->SetXTitle("cos(#theta)");
    h_costheta->SetYTitle("Counts");
    h_costheta->SetTitle(Form("MC Cosine of Angle between Trigger Layer %d and %d", trigger0, trigger1));
    h_costheta->SetDirectory(0);
    TF1* f1 = new TF1("f1", "x^2", 0, 1);
    for (int i = 0; i < 1e6; ++i) {
        double x0 = gRandom->Uniform(-HBU_X*1.5, HBU_X*1.5);
        double y0 = gRandom->Uniform(-HBU_Y*0.5, HBU_Y*0.5);
        double costheta = f1->GetRandom();
        double tantheta = sqrt((1/costheta/costheta) - 1);
        double phi = gRandom->Uniform(-3.14, 3.14);
        double x1 = x0 + tantheta * cos(phi) * abs(z_layer_cosmic(trigger0) - z_layer_cosmic(trigger1));
        double y1 = y0 + tantheta * sin(phi) * abs(z_layer_cosmic(trigger0) - z_layer_cosmic(trigger1));
        if (abs(x1) > HBU_X*1.5 || abs(y1) > HBU_Y*0.5) continue;
        h_costheta->Fill(costheta);
    }
    h_costheta->Scale(1.0 / h_costheta->Integral());
    return h_costheta;
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
    TF1* fitLine = new TF1("fitLine", "[0]*x + [1]", 0, 1602);
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
std::tuple <double, double, double, int> FitMuonTrack_withOffset(TH2D* h2_display, double* x_offset) {
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
                int layer = inverse_z_layer_cosmic(z_val);
                if (layer < 0) continue; // Skip if layer is invalid
                double x_val = h2_display->GetYaxis()->GetBinCenter(j) - x_offset[layer];
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
    TF1* fitLine = new TF1("fitLine", "[0]*x + [1]", 0, 1602);
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
void AllChannelSave(const char* filename, TH1D* h_ADC_MuonTrack[Layer_No][chip_No][channel_No], TH1D* h_ADC_NotMuonTrack[Layer_No][chip_No][channel_No], std::string tag= "Save") {
    if (tag.find("Save") != std::string::npos){
        TFile *fout = new TFile(filename, "RECREATE");
        for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
            fout->mkdir(Form("Layer_%d", i_layer));
            fout->cd(Form("Layer_%d", i_layer));
            for (int i_chip = 0; i_chip < chip_No; ++i_chip) {
                fout->mkdir(Form("Layer_%d/Chip_%d",i_layer,i_chip));
                fout->cd(Form("Layer_%d/Chip_%d", i_layer, i_chip));
                for (int i_channel = 0; i_channel < channel_No; ++i_channel) {
                    if (h_ADC_MuonTrack[i_layer][i_chip][i_channel]) {
                        h_ADC_MuonTrack[i_layer][i_chip][i_channel]->Write();
                    }
                    if (h_ADC_NotMuonTrack[i_layer][i_chip][i_channel]) {
                        h_ADC_NotMuonTrack[i_layer][i_chip][i_channel]->Write();
                    }
                }
            }
        }
        fout->Close();
    }
    if (tag.find("Print") != std::string::npos){
        for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
            if (gSystem->AccessPathName(Form("Layer_%d",i_layer))) {
                gSystem->mkdir(Form("Layer_%d",i_layer), true);
            }
            for (int i_chip = 0; i_chip < chip_No; ++i_chip) {
                if (gSystem->AccessPathName(Form("Layer_%d/Chip_%d",i_layer,i_chip))) {
                    gSystem->mkdir(Form("Layer_%d/Chip_%d",i_layer,i_chip), true);
                }
                for (int i_channel = 0; i_channel < channel_No; ++i_channel) {
                    TCanvas *c = new TCanvas(Form("c_Layer%d_Chip%d_Channel%d", i_layer, i_chip, i_channel), Form("Layer %d Chip %d Channel %d", i_layer, i_chip, i_channel), 800, 600);
                    if (h_ADC_MuonTrack[i_layer][i_chip][i_channel]) {
                        h_ADC_MuonTrack[i_layer][i_chip][i_channel]->SetTitle(Form("Layer %d Chip %d Channel %d ADC -Ped Distribution", i_layer, i_chip, i_channel));
                        h_ADC_MuonTrack[i_layer][i_chip][i_channel]->GetXaxis()->SetRangeUser(-40,2200);
                        h_ADC_MuonTrack[i_layer][i_chip][i_channel]->GetXaxis()->SetTitle("ADC - Pedestal");
                        h_ADC_MuonTrack[i_layer][i_chip][i_channel]->GetYaxis()->SetTitle("Counts");
                        h_ADC_MuonTrack[i_layer][i_chip][i_channel]->SetLineColor(kBlue);
                        h_ADC_MuonTrack[i_layer][i_chip][i_channel]->Draw();
                    }
                    if (h_ADC_NotMuonTrack[i_layer][i_chip][i_channel]) {
                        h_ADC_NotMuonTrack[i_layer][i_chip][i_channel]->SetLineColor(kRed);
                        h_ADC_NotMuonTrack[i_layer][i_chip][i_channel]->Draw("SAME");
                    }
                    TLegend *legend = new TLegend(0.7, 0.7, 0.9, 0.9);
                    legend->SetBorderSize(0);
                    legend->SetHeader(Form("Layer %d Chip %d Channel %d", i_layer, i_chip, i_channel));
                    if (h_ADC_MuonTrack[i_layer][i_chip][i_channel]) {
                        legend->AddEntry(h_ADC_MuonTrack[i_layer][i_chip][i_channel], "Matched to Muon Track", "l");
                    }
                    if (h_ADC_NotMuonTrack[i_layer][i_chip][i_channel]) {
                        legend->AddEntry(h_ADC_NotMuonTrack[i_layer][i_chip][i_channel], "Not Matched to Muon Track", "l");
                    }                   
                    legend->Draw();
                    c->SaveAs(Form("Layer_%d/Chip_%d/Channel_%d.png", i_layer, i_chip, i_channel));
                    delete c;
                    delete legend;
                }
            }
        }
    } else {
        std::cout << "Invalid tag for AllChannelSave: " << tag << std::endl;
    }
}
void AllLayerSave(const char* filename, TH1D* h_residual_x[Layer_No], TH1D* h_residual_y[Layer_No], std::string tag = "Save") {
    if (tag.find("Save") != std::string::npos){
        TFile *fout = new TFile(filename, "RECREATE");
        for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
            fout->mkdir(Form("Layer_%d", i_layer));
            fout->cd(Form("Layer_%d", i_layer));
            if (h_residual_x[i_layer]) {
                h_residual_x[i_layer]->Write(Form("Residual_X_Layer_%d", i_layer));
            }
            if (h_residual_y[i_layer]) {
                h_residual_y[i_layer]->Write(Form("Residual_Y_Layer_%d", i_layer));
            }
        }
        fout->Close();
    } 
    if (tag.find("Print") != std::string::npos){
        for (int i_layer = 0; i_layer < Layer_No; ++i_layer) {
            if (gSystem->AccessPathName(Form("Layer_%d",i_layer)))
                gSystem->mkdir(Form("Layer_%d",i_layer), true);
            TCanvas *c = new TCanvas(Form("c_Layer%d", i_layer), Form("Layer %d", i_layer), 800, 600);
            if (h_residual_x[i_layer]) {
                h_residual_x[i_layer]->SetTitle(Form("Layer %d Residual X Distribution", i_layer));
                h_residual_x[i_layer]->GetXaxis()->SetTitle("Residual X [mm]");
                h_residual_x[i_layer]->GetYaxis()->SetTitle("Counts");
                h_residual_x[i_layer]->SetLineColor(kBlue);
                h_residual_x[i_layer]->Draw();
            }
            if (h_residual_y[i_layer]) {
                h_residual_y[i_layer]->SetLineColor(kRed);
                h_residual_y[i_layer]->Draw("SAME");
            }
            TLegend *legend = new TLegend(0.7, 0.7, 0.9, 0.9);
            legend->SetBorderSize(0);
            legend->SetHeader(Form("Layer %d", i_layer));
            if (h_residual_x[i_layer]) {
                legend->AddEntry(h_residual_x[i_layer], "Residual X", "l");
            }
            if (h_residual_y[i_layer]) {
                legend->AddEntry(h_residual_y[i_layer], "Residual Y", "l");
            }
            legend->Draw();
            c->SaveAs(Form("Layer_%d/Residuals_offset.png", i_layer));
            delete c;
            delete legend;
        }
    } else {
        std::cout << "Invalid tag for AllLayerSave: " << tag << std::endl;
    }
}





int raw2Root::forMuon_MC(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1, double* x_offset, double* y_offset){
    //string str_root=find_datname(str_in);
    //string str_out=outputDir+"/"+"cos_ana.root";
    string str_out=output_file;
    TFile *fin,*fout;
    TTree *tree_in,*tree_out;
    // require the 0.8 MIP signal exist on the trigger layer
    // Create TFile first, then initialize tree
    TFile *fout1 = new TFile("MCTrack.root", "RECREATE");
    
    MCTrack mc_track(x_offset, y_offset);
    mc_track.InitializeTree(); // Initialize tree after file is created
    mc_track.SetTriggerLayers(trigger_layer0, trigger_layer1);
    int Nevents = 1000000; // Number of events to generate
    mc_track.GenerateTracks(Nevents);
    
    fout1->cd(); // Ensure we're in the correct directory
    mc_track.out_tree->Write();
    fout1->Close();
    delete fout1;
    
    std::cout << "Generated " << Nevents << " events with trigger layers " << trigger_layer0 << " and " << trigger_layer1 << std::endl;
    
    // Now read the tree back for analysis
    TFile *finMC = new TFile("MCTrack.root", "READ");
    TTree *mc_tree = (TTree*)finMC->Get("MCTrack");
    
    // Create new vectors for reading the data
    std::vector<int> *hit_layers = nullptr;
    std::vector<int> *hit_chips = nullptr;
    std::vector<int> *hit_channels = nullptr;
    double cos_theta, phi;
    double x_trigger0, y_trigger0, x_trigger1, y_trigger1;
    double hit_position_x[40];
    double hit_position_y[40];
    
    // Set branch addresses for reading
    mc_tree->SetBranchAddress("hit_layers", &hit_layers);
    mc_tree->SetBranchAddress("hit_chips", &hit_chips);
    mc_tree->SetBranchAddress("hit_channels", &hit_channels);
    mc_tree->SetBranchAddress("cos_theta", &cos_theta);
    mc_tree->SetBranchAddress("phi", &phi);
    mc_tree->SetBranchAddress("x_trigger0", &x_trigger0);
    mc_tree->SetBranchAddress("y_trigger0", &y_trigger0);
    mc_tree->SetBranchAddress("x_trigger1", &x_trigger1);
    mc_tree->SetBranchAddress("y_trigger1", &y_trigger1);
    mc_tree->SetBranchAddress("hit_position_x", hit_position_x);
    mc_tree->SetBranchAddress("hit_position_y", hit_position_y);
    
    std::vector<int> MuonCandidate;
    // std::vector<double> zx_chi2;
    // std::vector<double> zy_chi2;
    TFile *fout2 = new TFile("MuonCandidate2_MC.root","RECREATE");
    TCanvas *c2 = new TCanvas("c2","c2",800,600);
    c2->SaveAs("MuonCandidate2.pdf(");
    TH1D *h_chi2perndf_x = new TH1D("h_chi2perndf_x","chi2/ndf of xz plane;chi2/ndf",1000,0,50);
    TH1D *h_nHits = new TH1D("h_nHits_x","nHits;nHits",100,0,100);
    TH2D *h2_nHits_costheta = new TH2D("h2_nHits_costheta","nHits vs cos#theta;nHits;cos#theta",100,0,100,20,0,1);
    TH1D *h_slope_x = new TH1D("h_slope_x","slope of xz plane;tan#theta",50,-1,1);
    TH1D *h_intercept_x = new TH1D("h_intercept_x","intercept of xz plane;intercept",100,-500,500);
    TH1D *h_triggerlayer0_x = new TH1D("h_triggerlayer0_x","trigger layer 0 x;X [mm]",100,-500,500);
    TH1D *h_triggerlayer1_x = new TH1D("h_triggerlayer1_x","trigger layer 1 x;X [mm]",100,-500,500);
    TH1D *h_chi2perndf_y = new TH1D("h_chi2perndf_y","chi2/ndf of yz plane;chi2/ndf",1000,0,50);
    TH1D *h_slope_y = new TH1D("h_slope_y","slope of yz plane;tan#theta",50,-1,1);
    TH1D *h_intercept_y = new TH1D("h_intercept_y","intercept of yz plane;intercept",100,-500,500);
    TH1D *h_triggerlayer0_y = new TH1D("h_triggerlayer0_y","trigger layer 0 y;Y [mm]",100,-500,500);
    TH1D *h_triggerlayer1_y = new TH1D("h_triggerlayer1_y","trigger layer 1 y;Y [mm]",100,-500,500);
    TH1D *h_nHits_full = new TH1D("h_nHits_xy","nHits ;nHits",100,0,100);
    TH2D *h2_trigger0_xy = new TH2D("h2_trigger0_xy","trigger0_xy;X [mm];Y [mm]",100,-500,500,100,-500,500);
    TH2D *h2_trigger1_xy = new TH2D("h2_trigger1_xy","trigger1_xy;X [mm];Y [mm]",100,-500,500,100,-500,500);
    TH2D *h2_trigger0_xy_chi2_under5 = new TH2D("h2_trigger0_xy_chi2_under5","trigger0_xy_chi2_under5;X [mm];Y [mm]",100,-500,500,100,-500,500);
    TH1D *h_costheta = new TH1D("h_costheta","cos#theta;cos#theta",100,0,1);
    TH1D *h_phi = new TH1D("h_phi","phi;phi",100,-3.14,3.14);
    TH1D *h_costheta_chi2_under5 = new TH1D("h_costheta_chi2_under5","cos#theta under chi2/ndf < 5;cos#theta",100,0,1);
    TH1D *h_phi_chi2_under5 = new TH1D("h_phi_chi2_under5","phi under chi2/ndf < 5;phi",100,-3.14,3.14);
    std::cout << "Start Looping over events" << std::endl;
    TEfficiency *efficiency3 = new TEfficiency("efficiency3","efficiency3",Layer_No*chip_No*channel_No,0,Layer_No*chip_No*channel_No);
    TEfficiency *efficiency4 = new TEfficiency("efficiency4","efficiency4",Layer_No*chip_No*channel_No,0,Layer_No*chip_No*channel_No);
    TH1D * h_residual_x [Layer_No];
    TH1D * h_residual_y [Layer_No];
    TH2D * h2_residual_x[Layer_No];
    TH2D * h2_residual_y[Layer_No];
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        sprintf(char_tmp,"h_residual_x_%d",i_layer);
        h_residual_x[i_layer] = new TH1D(char_tmp,char_tmp,100,-50,50);
        h_residual_y[i_layer] = new TH1D(char_tmp,char_tmp,100,-50,50);
        h_residual_x[i_layer]->SetDirectory(0);
        h_residual_y[i_layer]->SetDirectory(0);
        sprintf(char_tmp,"h2_residual_x_%d",i_layer);
        h2_residual_x[i_layer] = new TH2D(char_tmp,char_tmp,18,-HBU_X*3/2,HBU_X*3/2,1000,-HBU_X*3/2,HBU_X*3/2);
        sprintf(char_tmp,"h2_residual_y_%d",i_layer);
        h2_residual_y[i_layer] = new TH2D(char_tmp,char_tmp,18,-HBU_Y/2,HBU_Y/2,1000,-HBU_Y/2,HBU_Y/2);
        h2_residual_x[i_layer]->SetDirectory(0);
        h2_residual_y[i_layer]->SetDirectory(0);
    }

    for (int i = 0; i < mc_tree->GetEntries(); ++i) {
        if((i%1000)==0)cout<<i<<" out of "<<mc_tree->GetEntries()<<endl;
        mc_tree->GetEntry(i);
        
        // Ensure vectors are valid
        if (!hit_layers || !hit_chips || !hit_channels) {
            continue;
        }
        
        TCanvas *c_2D = new TCanvas("c_2D", "c_2D", 48, 130, 1000, 723);
        c_2D->Divide(1,2);
            c_2D->cd(1)->SetRightMargin(0.3);
            // gStyle->SetOptStat(0);
            TH2D *h2_display_zx=new TH2D("display_zy","display_zy",534,0,1602,18,-9*40.3,9*40.3);
            h2_display_zx->SetDirectory(0);
            // h2_display_zx->GetXaxis()->SetRangeUser(0,800);
            h2_display_zx->GetXaxis()->SetTitle("Z [mm]");
            h2_display_zx->GetYaxis()->SetTitle("X [mm]");
            // h2_display_zx->GetXaxis()->SetTitleOffset(1.2);
            // h2_display_zx->GetYaxis()->SetTitleOffset(1.2);
            h2_display_zx->GetXaxis()->SetTitleSize(0.05);
            h2_display_zx->GetYaxis()->SetTitleSize(0.05);
            TH2D *h2_display_zy=new TH2D("display_zy","display_zy",534,0,1602,18,-9*40.3,9*40.3);
            h2_display_zy->SetDirectory(0);
            // h2_display_zy->GetXaxis()->SetRangeUser(0,800);
            h2_display_zy->GetXaxis()->SetTitle("Z [mm]");
            h2_display_zy->GetYaxis()->SetTitle("Y [mm]");
            // h2_display_zy->GetXaxis()->SetTitleOffset(1.2);
            // h2_display_zy->GetYaxis()->SetTitleOffset(1.2);
            h2_display_zy->GetXaxis()->SetTitleSize(0.05);
            h2_display_zy->GetYaxis()->SetTitleSize(0.05);
            
            for (int i_hit = 0; i_hit < hit_layers->size(); ++i_hit) {
                int layer, chip, channel;
                layer = hit_layers->at(i_hit);
                chip = hit_chips->at(i_hit);
                channel = hit_channels->at(i_hit);
                if (layer < 0 || layer >= Layer_No || chip < 0 || chip >= chip_No || channel < 0 || channel >= channel_No) {
                    std::cout << "Error: Invalid hit data at index " << i_hit << ": layer=" << layer << ", chip=" << chip << ", channel=" << channel << std::endl;
                    continue; // Skip invalid hits
                }
                // decode_cellid(cellID->at(i_hit),layer,chip,channel);
                double hitE=0;
                if (ExcludeCh(layer,chip,channel)) continue;
                // hitE=( HG_Charge->at(i_hit) -ped_new[layer][chip][channel] )*MIP_E/MIP[layer][chip][channel];
                // Apply x_offset for layer-specific offset correction
                double x_corrected = Pos_X(channel,chip);
                h2_display_zx->Fill(z_layer_cosmic(layer),x_corrected);
                h2_display_zy->Fill(z_layer_cosmic(layer),Pos_Y(channel,chip));
            }
            int nhits = hit_layers->size();
            double trigger0_z = z_layer_cosmic(trigger_layer0);
            double trigger1_z = z_layer_cosmic(trigger_layer1);
            h2_display_zx->SetTitle(Form("Event %d",i));
            // h2_display_zx->GetYaxis()->SetRangeUser(0,1000);
            // h2_display_zx->Draw("colz");
            std::tuple <double,double,double, int> fit_result = FitMuonTrack_withOffset(h2_display_zx, x_offset);
            h_chi2perndf_x->Fill(std::get<2>(fit_result));
            h_nHits->Fill(nhits);
            h_slope_x->Fill(std::get<0>(fit_result));
            h_intercept_x->Fill(std::get<1>(fit_result));
            double trigger_layer0_x = std::get<0>(fit_result) * trigger0_z + std::get<1>(fit_result);
            double trigger_layer1_x = std::get<0>(fit_result) * trigger1_z + std::get<1>(fit_result);
            h_triggerlayer0_x->Fill(trigger_layer0_x);
            h_triggerlayer1_x->Fill(trigger_layer1_x);
            // FitMuonTrack(h2_display_zx);
            // c2->SaveAs(Form("MuonCandidate.pdf",i));
            // c_2D->cd(2);
            c_2D->cd(2)->SetRightMargin(0.3);
            h2_display_zy->SetTitle(Form("Event %d",i));
            // h2_display_zy->GetYaxis()->SetRangeUser(0,1000);
            // h2_display_zy->Draw("colz");
            // FitMuonTrack(h2_display_zy);
            std::tuple <double,double,double, int> fit_result2 = FitMuonTrack_withOffset(h2_display_zy, y_offset);
            h_chi2perndf_y->Fill(std::get<2>(fit_result2));
            // h_nHits_y->Fill(std::get<3>(fit_result2));
            h_slope_y->Fill(std::get<0>(fit_result2));
            h_intercept_y->Fill(std::get<1>(fit_result2));
            double trigger_layer0_y = std::get<0>(fit_result2) * trigger0_z + std::get<1>(fit_result2);
            double trigger_layer1_y = std::get<0>(fit_result2) * trigger1_z + std::get<1>(fit_result2);
            h_triggerlayer0_y->Fill(trigger_layer0_y);
            h_triggerlayer1_y->Fill(trigger_layer1_y);
            h2_trigger0_xy->Fill(trigger_layer0_x,trigger_layer0_y);
            h2_trigger1_xy->Fill(trigger_layer1_x,trigger_layer1_y);
            double costheta = std::sqrt(1.0 / (1.0 + std::pow(std::get<0>(fit_result), 2) + std::pow(std::get<0>(fit_result2), 2)));
            double phi = std::atan2(std::get<0>(fit_result2), std::get<0>(fit_result));
            h_costheta->Fill(costheta);
            h2_nHits_costheta->Fill(nhits, costheta);
            h_phi->Fill(phi);
            if (std::get<2>(fit_result) < 5 && std::get<2>(fit_result2) < 5){
                h2_trigger0_xy_chi2_under5->Fill(trigger_layer0_x,trigger_layer0_y);
                h_costheta_chi2_under5->Fill(costheta);
                h_phi_chi2_under5->Fill(phi);
            }
            // c_2D->SaveAs("MuonCandidate2.pdf");
            // c_2D->SaveAs(Form("MuonCandidate_%d.png",i));
            //denominator events
            // if ( trigger0_MIP_exist == 1 && trigger1_MIP_exist == 1 && 
            if ( std::get<2>(fit_result) < 5 && std::get<2>(fit_result2) < 5){
                // abs(trigger_layer0_x - trigger0_xy.first) < 20 &&
                // abs(trigger_layer0_y - trigger0_xy.second) < 20 &&
                // abs(trigger_layer1_x - trigger1_xy.first) < 20 &&
                // abs(trigger_layer1_y - trigger1_xy.second) < 20){
                    // passing cell 
                    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
                        double x = std::get<0>(fit_result) * z_layer_cosmic(i_layer) + std::get<1>(fit_result);
                        double y = std::get<0>(fit_result2) * z_layer_cosmic(i_layer) + std::get<1>(fit_result2);
                        
                        // Apply offset correction to expected position
                        double x_expected = x + x_offset[i_layer];
                        double y_expected = y + y_offset[i_layer];
                        
                        int chip =0;
                        int channel = 0;
                        int i = x_expected/40.3;
                        int j = y_expected/40.3; // if y= -80, j =
                        if ( abs(x_expected) > HBU_X*1.5 || abs(y_expected) > HBU_Y*0.5) continue;
                        inverse(x_expected,y_expected,chip,channel);
                        if (chip < 0 || chip >= chip_No || channel < 0 || channel >= channel_No) continue;
                        if ( abs(x_expected - Pos_X(channel,chip)) <  17 && abs(y_expected - Pos_Y(channel,chip)) < 17) {
                            bool is_Hit = false;
                            for (int i_hit = 0; i_hit < hit_layers->size(); ++i_hit) {
                                if (hit_layers->at(i_hit) == i_layer && 
                                    hit_chips->at(i_hit) == chip && 
                                    hit_channels->at(i_hit) == channel) {
                                    is_Hit = true;
                                    break;
                                }
                            }
                            efficiency4->Fill(is_Hit, i_layer*chip_No*channel_No + chip*channel_No + channel);
                        }

                        int n_MIP = 0;
                        // int chips, channels;
                            h_residual_x[i_layer]->Fill(Pos_X(channel,chip) - x_expected);
                            h2_residual_x[i_layer]->Fill(Pos_X(channel,chip),x_expected);
                            h_residual_y[i_layer]->Fill(Pos_Y(channel,chip) - y_expected);
                            h2_residual_y[i_layer]->Fill(Pos_Y(channel,chip),y_expected);
                    }

            }
            delete c_2D;
            delete h2_display_zx;
            delete h2_display_zy;
    }
    c2->SaveAs("MuonCandidate2.pdf)");
    // for (int i = 0; i < MuonCandidate.size(); ++i){
    //     cout << "MuonCandidate: " << MuonCandidate[i] << endl;
    // }
    double x2_offset[40];
    double y2_offset[40];
    for (int i = 0; i < 40; ++i){
        x2_offset[i] = h_residual_x[i]->GetMean();
        y2_offset[i] = h_residual_y[i]->GetMean();
    }
    // AllChannelSave("MuonADC_offset.root",h_ADC_MuonTrack,h_ADC_NotMuonTrack,saveornot);
    AllLayerSave("MuonResidual_offset.root",h_residual_x,h_residual_y,saveornot);

    TFile *fout3 = new TFile("MuonResidual2_offset.root","RECREATE");
    fout3->cd();
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        h2_residual_x[i_layer]->Write();
        h2_residual_y[i_layer]->Write();
    }
    
    fout2->cd();
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
    c3->SaveAs("MuonCandidate2_offset_chi2.png");
    c3->SetLogy();
    // h_nHits_full->SetLineColor(kRed);
    // h_nHits_full->SetLineWidth(2);
    h_nHits->SetLineColor(kBlue);
    h_nHits->SetLineWidth(2);
    // h_nHits_full->Draw("hist");
    h_nHits->Draw("hist");
    // h_nHits_full->GetXaxis()->SetTitle("nHits");
    // h_nHits_full->GetYaxis()->SetTitle("Counts");
    TLatex *latex = new TLatex();
    latex->SetTextSize(0.03);
    // latex->SetTextColor(kRed);
    latex->SetTextFont(42);
    latex->DrawLatexNDC(0.2, 0.85, Form("Run %d", _Run_No));
    // latex->DrawLatexNDC(0.75, 0.6, Form("Time %s", 
    // latex->DrawLatexNDC(0.2, 0.8, Form("Full Data %d Events" , tree_in->GetEntries()));
    latex->DrawLatexNDC(0.2, 0.75, Form("MuonCandidate %d Events" , MuonCandidate.size()));
    TLegend *leg2 = new TLegend(0.6,0.7,0.85,0.85);
    // leg2->AddEntry(h_nHits_full,"full data","l");
    leg2->AddEntry(h_nHits,"MuonCandidate","l");
    leg2->SetBorderSize(0);
    leg2->SetFillColor(0);
    leg2->Draw();
    c3->SaveAs("MuonCandidate2_offset_nHits.png");
    // TEfficiency *efficiency = new TEfficiency(*h_triggerID_MuonCandidate, *h_triggerID_full);
    // TCanvas *c_eff = new TCanvas("c_eff","c_eff",800,600);
    // efficiency->SetTitle("MuonCandidate Efficiency; Trigger ID; Efficiency");
    // // efficiency->SetLineColor(kRed);
    // efficiency->Draw();
    // c_eff->SaveAs("MuonCandidate2_offset_efficiency.png");
    // TCanvas *c4 = new TCanvas("c4","c4",800,600);
    // c4->Divide(2,1);
    // c4->cd(1);
    // h_triggerID_full->SetLineColor(kRed);
    // h_triggerID_full->SetLineWidth(2);
    // h_triggerID_full->GetXaxis()->SetTitle("Trigger ID");
    // h_triggerID_full->GetYaxis()->SetTitle("Events/TriggerID");
    // h_triggerID_full->Scale(1./(h_triggerID_full->GetXaxis()->GetXmax()/h_triggerID_full->GetNbinsX())); // Scale
    // h_triggerID_full->Draw("hist");
    // c4->cd(2);
    // h_triggerID_MuonCandidate->SetLineColor(kBlue);
    // h_triggerID_MuonCandidate->SetLineWidth(2);
    // h_triggerID_MuonCandidate->GetXaxis()->SetTitle("Trigger ID");
    // h_triggerID_MuonCandidate->GetYaxis()->SetTitle("Events/TriggerID");
    // h_triggerID_MuonCandidate->Scale(1./(h_triggerID_MuonCandidate->GetXaxis()->GetXmax()/h_triggerID_MuonCandidate->GetNbinsX())); // Scale
    // h_triggerID_MuonCandidate->SetTitle("MuonCandidate Trigger ID Distribution");
    // h_triggerID_MuonCandidate->Draw("hist");
    // c4->SaveAs("MuonCandidate2_offset_triggerID.png");
    // TCanvas *c51 = new TCanvas("c51","c51",800,1500);
    // c51->Divide(1,3);
    // c51->cd(1);
    // TLatex *latex2 = new TLatex();
    // latex2->SetTextSize(0.03);
    // latex2->SetTextFont(42);
    // latex2->DrawLatexNDC(0.2, 0.85, Form("Run %d", _Run_No));
    // latex2->DrawLatexNDC(0.2, 0.8, Form("Full Data %d Events" , tree_in->GetEntries()));
    // latex2->DrawLatexNDC(0.2, 0.75, Form("MuonCandidate %d Events" , MuonCandidate.size()));
    // h_time_full->SetLineColor(kRed);
    // h_time_full->SetLineWidth(2);
    // h_time_full->GetXaxis()->SetTitle("Event Time [s]");
    // h_time_full->GetYaxis()->SetTitle("Hz");
    // h_time_full->SetTitle("Full Data Event Time Distribution");
    // h_time_full->Scale(1./(h_time_full->GetXaxis()->GetXmax()/h_time_full->GetNbinsX())); // Scale to Hz
    // h_time_full->Draw("hist");
    // c51->cd(2);
    // h_time_MuonCandidate->SetLineColor(kBlue);
    // h_time_MuonCandidate->SetLineWidth(2);
    // h_time_MuonCandidate->GetXaxis()->SetTitle("Event Time [s]");
    // h_time_MuonCandidate->GetYaxis()->SetTitle("Hz");
    // h_time_MuonCandidate->SetTitle("MuonCandidate Event Time Distribution");
    // h_time_MuonCandidate->Scale(1./(h_time_MuonCandidate->GetXaxis()->GetXmax()/h_time_MuonCandidate->GetNbinsX())); // Scale to Hz
    // h_time_MuonCandidate->Draw("hist");
    // c51->cd(3);
    // TEfficiency *efficiency2 = new TEfficiency(*h_time_MuonCandidate, *h_time_full);
    // // TCanvas *c_eff2 = new TCanvas("c_eff2","c_eff2",800,600);
    // efficiency2->SetTitle("MuonCandidate Efficiency; Event Time [s]; Efficiency");
    // // efficiency2->SetLineColor(kRed);
    // efficiency2->Draw();
    // // c51->SaveAs("MuonCandidate2_offset_time.png");
    // TCanvas *c5 = new TCanvas("c5","c5",800,1500);
    // c5->Divide(1,3);
    // c5->cd(1);
    // h_time_full_bin1->SetLineColor(kRed);
    // h_time_full_bin1->SetLineWidth(2);
    // h_time_full_bin1->GetXaxis()->SetTitle("Event Time [s]");
    // h_time_full_bin1->GetYaxis()->SetTitle("Hz");
    // h_time_full_bin1->SetTitle("Full Data Event Time Distribution (bin 1)");
    // h_time_full_bin1->Scale(1./(h_time_full_bin1->GetXaxis()->GetXmax()/h_time_full_bin1->GetNbinsX())); // Scale
    // h_time_full_bin1->Draw("hist");
    // c5->cd(2);
    // h_time_MuonCandidate_bin1->SetLineColor(kBlue);
    // h_time_MuonCandidate_bin1->SetLineWidth(2);
    // h_time_MuonCandidate_bin1->GetXaxis()->SetTitle("Event Time [s]");
    // h_time_MuonCandidate_bin1->GetYaxis()->SetTitle("Hz");
    // h_time_MuonCandidate_bin1->SetTitle("MuonCandidate Event Time Distribution (bin 1)");
    // h_time_MuonCandidate_bin1->Scale(1./(h_time_MuonCandidate_bin1->GetXaxis()->GetXmax()/h_time_MuonCandidate_bin1->GetNbinsX())); // Scale
    // h_time_MuonCandidate_bin1->Draw("hist");
    // c5->cd(3);
    // TEfficiency *efficiency31 = new TEfficiency(*h_time_MuonCandidate_bin1, *h_time_full_bin1);
    // // TCanvas *c_eff2 = new TCanvas("c_eff2","c_eff2",800,600);
    // efficiency31->SetTitle("MuonCandidate Efficiency (bin 1); Event Time [s]; Efficiency");
    // // efficiency3->SetLineColor(kRed);
    // efficiency31->Draw();
    // c5->SaveAs("MuonCandidate2_time_bin1.png");
    // c_eff2->SaveAs("MuonCandidate2_time_efficiency.png");
    // TCanvas *c6 = new TCanvas("c6","c6",8000,600);
    // efficiency3->SetTitle("Efficiency of 1/2 MIP in each cell; Layer*Chip*Channel; Efficiency");
    // // efficiency3->SetLineColor(kRed);
    // // efficiency3->SetMarkerColor(kRed);
    // // efficiency3->SetMarkerStyle(20);
    // // efficiency3->SetMarkerSize(0.5);
    // efficiency3->Draw();
    // c6->Update();
    // auto graph = efficiency3->GetPaintedGraph();
    // graph->GetXaxis()->SetRangeUser(0, Layer_No*chip_No*channel_No);
    // graph->Draw("AP");
    // for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
    //     TLine *line = new TLine(i_layer*chip_No*channel_No, 0, i_layer*chip_No*channel_No, 1);
    //     line->SetLineColor(kRed);
    //     line->SetLineStyle(2);
    //     line->Draw("same");
    //     TLatex *latex_layer = new TLatex();
    //     latex_layer->SetTextSize(0.03);
    //     latex_layer->SetTextFont(42);
    //     if (i_layer == trigger_layer0 || i_layer == trigger_layer1){
    //         latex_layer->SetTextColor(kBlue);
    //         latex_layer->DrawLatex(i_layer*chip_No*channel_No+ chip_No*channel_No*0.3, 1.09, Form("Trigger Layer"));
    //     }else{
    //         latex_layer->SetTextColor(kBlack);
    //     }
    //     latex_layer->DrawLatex(i_layer*chip_No*channel_No+ chip_No*channel_No*0.3, 1.05, Form("Layer %d", i_layer));
    // }
    // c6->Update();
    // c6->Modified();
    // c6->SaveAs("MuonCandidate2_offset_efficiency3.png");
    // for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
    //     TCanvas *c1 = new TCanvas(Form("c1_layer%d",i_layer),Form("c1_layer%d",i_layer),800,600);
    //     graph->GetXaxis()->SetRangeUser(i_layer*chip_No*channel_No, (i_layer+1)*chip_No*channel_No);
    //     graph->SetTitle(Form("Efficiency of Layer %d; Chip*Channel; Efficiency", i_layer));
    //     graph->Draw("AP");
    //     for (int i_chip = 0; i_chip < chip_No; ++i_chip){
    //         TLine *line = new TLine(i_layer*chip_No*channel_No + i_chip*channel_No, 0, i_layer*chip_No*channel_No + i_chip*channel_No, 1);
    //         line->SetLineColor(kRed);
    //         line->SetLineStyle(2);
    //         line->Draw("same");
    //         TLatex *latex_chip = new TLatex();
    //         latex_chip->SetTextSize(0.03);
    //         latex_chip->SetTextFont(42);
    //         latex_chip->DrawLatex(i_layer*chip_No*channel_No+ i_chip*channel_No+ channel_No*0.3, 1.05, Form("Chip %d", i_chip));
    //     }
    //     c1->Update();
    //     c1->Modified();
    //     if (gSystem->AccessPathName(Form("Layer_%d",i_layer))) {
    //         gSystem->mkdir(Form("Layer_%d",i_layer), true);
    //     }
    //     c1->SaveAs(Form("Layer_%d/MuonCandidate_offset_efficiency_layer%d.png", i_layer, i_layer));
    // }
    TCanvas *c7 = new TCanvas("c7","c7",8000,600);
    efficiency4->SetTitle("Efficiency of Hit Tag in each cell; Layer*Chip*Channel; Efficiency");
    // efficiency4->SetLineColor(kRed);
    // efficiency4->SetMarkerColor(kRed);
    // efficiency4->SetMarkerStyle(20);
    // efficiency4->SetMarkerSize(0.5);
    efficiency4->Draw();
    c7->Update();
    auto graph2 = efficiency4->GetPaintedGraph();
    graph2->GetXaxis()->SetRangeUser(0, Layer_No*chip_No*channel_No);
    graph2->Draw("AP");
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        TLine *line = new TLine(i_layer*chip_No*channel_No, 0, i_layer*chip_No*channel_No, 1);
        line->SetLineColor(kRed);
        line->SetLineStyle(2);
        line->Draw("same");
        TLatex *latex_layer = new TLatex();
        latex_layer->SetTextSize(0.03);
        latex_layer->SetTextFont(42);
        if (i_layer == trigger_layer0 || i_layer == trigger_layer1){
            latex_layer->SetTextColor(kBlue);
            latex_layer->DrawLatex(i_layer*chip_No*channel_No+ chip_No*channel_No*0.3, 1.09, Form("Trigger Layer"));
        }else{
            latex_layer->SetTextColor(kBlack);
        }
        latex_layer->DrawLatex(i_layer*chip_No*channel_No+ chip_No*channel_No*0.3, 1.05, Form("Layer %d", i_layer));
    }
    c7->Update();
    c7->Modified();
    c7->SaveAs("MuonCandidate2_offset_efficiency4.png");
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        TCanvas *c1 = new TCanvas(Form("c1_layer%d_hit",i_layer),Form("c1_layer%d_hit",i_layer),800,600);
        graph2->GetXaxis()->SetRangeUser(i_layer*chip_No*channel_No, (i_layer+1)*chip_No*channel_No);
        graph2->SetTitle(Form("Efficiency of Hit Tag in Layer %d; Chip*Channel; Efficiency", i_layer));
        graph2->Draw("AP");
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            TLine *line = new TLine(i_layer*chip_No*channel_No + i_chip*channel_No, 0, i_layer*chip_No*channel_No + i_chip*channel_No, 1);
            line->SetLineColor(kRed);
            line->SetLineStyle(2);
            line->Draw("same");
            TLatex *latex_chip = new TLatex();
            latex_chip->SetTextSize(0.03);
            latex_chip->SetTextFont(42);
            latex_chip->DrawLatex(i_layer*chip_No*channel_No+ i_chip*channel_No+ channel_No*0.3, 1.05, Form("Chip %d", i_chip));
            for (int i_channel = 0; i_channel < channel_No; ++i_channel){
                if (efficiency4->GetEfficiency(i_layer*chip_No*channel_No + i_chip*channel_No + i_channel) < 0.4 ){
                    TLatex *latex_channel = new TLatex();
                    latex_channel->SetTextSize(0.03);
                    latex_channel->SetTextFont(42);
                    latex_channel->SetTextColor(kRed);
                    latex_channel->DrawLatex(i_layer*chip_No*channel_No+ i_chip*channel_No+ i_channel, 0.3, Form("Channel %d", i_channel));
                }
            }
        }
        c1->Update();
        c1->Modified();
        if (gSystem->AccessPathName(Form("Layer_%d",i_layer))) {
            gSystem->mkdir(Form("Layer_%d",i_layer), true);
        }
        c1->SaveAs(Form("Layer_%d/MuonCandidate_offset_efficiency4_layer%d.png", i_layer, i_layer));
    }
    TCanvas *c8 = new TCanvas("c8","c8",800,600);
    h2_nHits_costheta->Draw("COLZ");
    h2_nHits_costheta->GetXaxis()->SetTitle("nHits");
    h2_nHits_costheta->GetYaxis()->SetTitle("cos(theta)");
    h2_nHits_costheta->SetTitle("nHits vs cos(theta) for Muon Candidates");
    c8->SaveAs("MuonCandidate2_offset_nHits_costheta.png");
    TCanvas *c9 = new TCanvas("c9","c9",800,600);
    h_costheta->SetLineColor(kRed);
    h_costheta->SetLineWidth(2);
    h_costheta->GetXaxis()->SetTitle("cos(theta)");
    h_costheta->GetYaxis()->SetTitle("Counts");
    h_costheta->Scale(1./(h_costheta->Integral()));
    h_costheta_chi2_under5->SetLineColor(kBlue);
    h_costheta_chi2_under5->SetLineWidth(2);
    h_costheta_chi2_under5->GetXaxis()->SetTitle("cos(theta)");
    h_costheta_chi2_under5->GetYaxis()->SetTitle("Counts");
    h_costheta_chi2_under5->Scale(1./(h_costheta_chi2_under5->Integral()));
    h_costheta->Draw("hist");
    h_costheta_chi2_under5->Draw("hist same");
    TH1D *h_costheta_MC = h_costheta2( trigger_layer0, trigger_layer1);
    h_costheta_MC->SetLineColor(kGreen);
    h_costheta_MC->SetLineWidth(2);
    h_costheta_MC->GetXaxis()->SetTitle("cos(theta)");
    h_costheta_MC->GetYaxis()->SetTitle("Counts");
    h_costheta_MC->Scale(1./(h_costheta_MC->Integral()));
    h_costheta_MC->Draw("hist same");
    TLegend *leg3 = new TLegend(0.2,0.6,0.5,0.9);
    leg3->AddEntry(h_costheta,"Muon Candidate cos(theta)","l");
    leg3->AddEntry(h_costheta_chi2_under5,"Muon Candidate cos(theta) #chi^{2}/NDF < 5","l");
    leg3->AddEntry(h_costheta_MC,"MC","l");
    leg3->SetBorderSize(0);
    leg3->SetFillColor(0);
    leg3->Draw();
    c9->SaveAs("MuonCandidate2_offset_costheta.png");
    h2_nHits_costheta->Write();
    // efficiency2->Write();
    h_chi2perndf_x->Write();
    h_slope_x->Write();
    h_intercept_x->Write();
    h_chi2perndf_y->Write();
    h_slope_y->Write();
    h_intercept_y->Write();
    h_triggerlayer0_x->Write();
    h_triggerlayer1_x->Write();
    h_triggerlayer0_y->Write();
    h_triggerlayer1_y->Write();
    h_nHits->Write();
    h_nHits_full->Write();
    h2_trigger0_xy->Write();
    h2_trigger1_xy->Write();
    h2_trigger0_xy_chi2_under5->Write();
    h_costheta->Write();
    h_phi->Write();
    h_costheta_chi2_under5->Write();
    h_phi_chi2_under5->Write();
    // h_triggerID_full->Write();
    // h_triggerID_MuonCandidate->Write();
    // h_time_full->Write();
    // h_time_MuonCandidate->Write();
    // h_time_full_bin1->Write();
    // h_time_MuonCandidate_bin1->Write();
    efficiency4->Write();
    // efficiency3->Write();

    // Save offset values to TTree
    TTree* offset_tree = new TTree("offset_values", "Applied Offset Values");
    int layer_id;
    double x_offset_val, y_offset_val;
    
    offset_tree->Branch("layer", &layer_id, "layer/I");
    offset_tree->Branch("x_offset", &x_offset_val, "x_offset/D");
    offset_tree->Branch("y_offset", &y_offset_val, "y_offset/D");
    
    for (int i = 0; i < 40; ++i) {
        layer_id = i;
        x_offset_val = x2_offset[i];
        y_offset_val = y2_offset[i];
        offset_tree->Fill();
    }
    
    offset_tree->Write();
    
    // Also save offset histograms
    TH1D *h_x_offset = new TH1D("h_x_offset", "Applied X Offset per Layer", 40, -0.5, 39.5);
    TH1D *h_y_offset = new TH1D("h_y_offset", "Applied Y Offset per Layer", 40, -0.5, 39.5);
    
    for (int i = 0; i < 40; ++i) {
        h_x_offset->SetBinContent(i+1, x2_offset[i]);
        h_y_offset->SetBinContent(i+1, y2_offset[i]);
    }
    h_x_offset->Write();
    h_y_offset->Write();
    
    fout2->Close();           
    fout->Close();
    return 1;
}
