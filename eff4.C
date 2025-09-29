#include "include/Global.h"

int trigger_layer0 = 4;
int trigger_layer1 = 14;

void eff4(){
    TFile *fMC = TFile::Open("run855-MC/MuonCandidate2_MC.root","READ");
    TFile *fdat = TFile::Open("run855_2/MuonCandidate2_offset.root","READ");
    TEfficiency *efficiency4_MC = (TEfficiency*)fMC->Get("efficiency4");
    TEfficiency *efficiency4 = (TEfficiency*)fdat->Get("efficiency4");
    TCanvas *c_compare = new TCanvas("c_compare","c_compare",8000,1200);
    c_compare->Divide(1,2);
    c_compare->cd(1);
    efficiency4_MC->SetTitle("Efficiency of DAQ ; Cell; Efficiency");
    efficiency4_MC->SetLineColor(kRed);
    // efficiency4_MC->SetMarkerColor(kRed);
    // efficiency4_MC->SetMarkerStyle(20);
    // efficiency4_MC->SetMarkerSize(0.5);
    efficiency4_MC->Draw();
    efficiency4->SetTitle("Efficiency of DAQ ; Cell; Efficiency");
    efficiency4->SetLineColor(kBlack);
    // efficiency4->SetMarkerColor(kBlack);
    // efficiency4->SetMarkerStyle(20);
    // efficiency4->SetMarkerSize(0.5);
    efficiency4->Draw("same");
    c_compare->Update();
    // c_compare->Modified();
    auto graph2 = efficiency4_MC->GetPaintedGraph();
    graph2->SetLineColor(kRed);
    graph2->GetXaxis()->SetRangeUser(0, Layer_No*chip_No*channel_No);
    graph2->GetYaxis()->SetRangeUser(0, 1);
    graph2->Draw("AP");
    auto graph1 = efficiency4->GetPaintedGraph();
    graph1->SetLineColor(kBlack);
    graph1->GetXaxis()->SetRangeUser(0, Layer_No*chip_No*channel_No);

    graph1->Draw("P same");
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
    c_compare->cd(2);
    graph2->SetTitle("Efficiency ratio ; Cell; Efficiency");
    graph1->SetTitle("Efficiency ratio ; Cell; Efficiency");
    
    // Create a new graph for the ratio
    TGraphAsymmErrors *graph1_new = new TGraphAsymmErrors();
    int npoints = graph1->GetN();
    Double_t x, y1, y2, e1_up, e1_down, e2_up, e2_down;
    
    for (int i = 0; i < npoints; i++) {
        graph1->GetPoint(i, x, y1);
        graph2->GetPoint(i, x, y2);
        e1_up = graph1->GetErrorYhigh(i);
        e1_down = graph1->GetErrorYlow(i);
        e2_up = graph2->GetErrorYhigh(i);
        e2_down = graph2->GetErrorYlow(i);
        if (y2 != 0) { // Avoid division by zero
            graph1_new->SetPoint(i, x, y1/y2);
            graph1_new->SetPointError(i, 0, 0, e1_down/y2, e1_up/y2); // Error propagation
        } else {
            graph1_new->SetPoint(i, x, 0); // Set to 0 if denominator is zero
            graph1_new->SetPointError(i, 0, 0, 0, 0); // No error if denominator is zero
        }
    }
    
    graph1_new->SetLineColor(kBlack);
    graph1_new->GetYaxis()->SetRangeUser(0, 1.1);
    graph1_new->Draw("AP");
    graph1_new->GetXaxis()->SetRangeUser(0, Layer_No*chip_No*channel_No);
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        TLine *line = new TLine(i_layer*chip_No*channel_No, 0, i_layer*chip_No*channel_No, 1.1);
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
    c_compare->Update();
    c_compare->Modified();
    c_compare->SaveAs("run855-MC/MuonCandidate2_efficiency4_compare.png");
    TGraphErrors *graph_average_ratio = new TGraphErrors();
    graph_average_ratio->SetTitle("Average Efficiency Ratio per Layer; Layer; Average Ratio");
    graph_average_ratio->SetMarkerStyle(20);
    graph_average_ratio->SetMarkerSize(1.0);
    for (int i_layer = 0; i_layer < Layer_No; ++i_layer){
        TCanvas *c1 = new TCanvas(Form("c1_layer%d_hit",i_layer),Form("c1_layer%d_hit",i_layer),800,600);
        c1->Divide(1,2);
        c1->cd(1);
        graph2->GetXaxis()->SetRangeUser(i_layer*chip_No*channel_No, (i_layer+1)*chip_No*channel_No);
        graph2->SetTitle(Form("Efficiency of DAQ in Layer %d; Chip*Channel; Efficiency", i_layer));
        graph2->Draw("AP");
        graph1->GetXaxis()->SetRangeUser(i_layer*chip_No*channel_No, (i_layer+1)*chip_No*channel_No);
        graph1->SetTitle(Form("Efficiency of DAQ in Layer %d; Chip*Channel; Efficiency", i_layer));
        graph1->Draw("P same");
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            TLine *line = new TLine(i_layer*chip_No*channel_No + i_chip*channel_No, 0, i_layer*chip_No*channel_No + i_chip*channel_No, 1);
            line->SetLineColor(kRed);
            line->SetLineStyle(2);
            line->Draw("same");
            TLatex *latex_chip = new TLatex();
            latex_chip->SetTextSize(0.03);
            latex_chip->SetTextFont(42);
            latex_chip->SetTextColor(kBlack);
            latex_chip->DrawLatex(i_layer*chip_No*channel_No+ i_chip*channel_No+ channel_No*0.3, 1.05, Form("Chip %d", i_chip));
        }
        c1->cd(2);
        graph1_new->GetXaxis()->SetRangeUser(i_layer*chip_No*channel_No, (i_layer+1)*chip_No*channel_No);
        graph1_new->SetTitle(Form("Efficiency ratio in Layer %d; Chip*Channel; Efficiency", i_layer));
        graph1_new->Draw("AP");
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            TLine *line = new TLine(i_layer*chip_No*channel_No + i_chip*channel_No, 0, i_layer*chip_No*channel_No + i_chip*channel_No, 1.1);
            line->SetLineColor(kRed);
            line->SetLineStyle(2);
            line->Draw("same");
            TLatex *latex_chip = new TLatex();
            latex_chip->SetTextSize(0.03);
            latex_chip->SetTextFont(42);
            latex_chip->SetTextColor(kBlack);
            latex_chip->DrawLatex(i_layer*chip_No*channel_No+ i_chip*channel_No+ channel_No*0.3, 1.05, Form("Chip %d", i_chip));
        }
        c1->Update();
        c1->Modified();
        if (gSystem->AccessPathName(Form("run855-MC/Layer_%d",i_layer))) {
            gSystem->mkdir(Form("run855-MC/Layer_%d",i_layer), true);
        }
        c1->SaveAs(Form("run855-MC/Layer_%d/MuonCandidate_compare_efficiency4_layer%d.png", i_layer, i_layer));
        // Calculate average ratio for the layer
        double sum_ratio = 0;
        double sum_squared = 0;
        int count = 0;
        for (int i_chip = 0; i_chip < chip_No; ++i_chip){
            for (int i_channel = 0; i_channel < channel_No; ++i_channel){
                int index = i_layer * chip_No * channel_No + i_chip * channel_No + i_channel;
                double ratio = graph1_new->GetY()[index];
                double error = graph1_new->GetErrorYhigh(index);
                if (ratio > 0) { // Only consider positive ratios
                    sum_ratio += ratio;
                    sum_squared += error * error; // Accumulate squared errors for uncertainty calculation
                    count++;
                }
            }
        }
        double average_ratio = (count > 0) ? sum_ratio / count : 0;
        double uncertainty = (count > 0) ? sqrt(sum_squared / count) : 0; // Calculate uncertainty
        graph_average_ratio->SetPoint(i_layer, i_layer, average_ratio);
        graph_average_ratio->SetPointError(i_layer, 0, uncertainty);
        std::cout << "Layer " << i_layer << ": Average Ratio = " << average_ratio << " ± " << uncertainty << std::endl;
    }
    TCanvas *c_average = new TCanvas("c_average", "Average Efficiency Ratio per Layer", 800, 600);
    graph_average_ratio->SetMarkerColor(kBlack);
    graph_average_ratio->SetLineColor(kBlack);
    graph_average_ratio->SetMarkerStyle(20);
    graph_average_ratio->SetMarkerSize(1.0);
    graph_average_ratio->GetXaxis()->SetRangeUser(0, Layer_No);
    // graph_average_ratio->GetYaxis()->SetRangeUser(0, 1.1);
    graph_average_ratio->SetTitle("Average Efficiency Ratio per Layer; Layer; Average Ratio");
    graph_average_ratio->Draw("AP");
    c_average->Update();
    c_average->Modified();
    c_average->SaveAs("run855-MC/MuonCandidate2_efficiency4_average_ratio.png");
}