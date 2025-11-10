const int chip_No = 9;
const int channel_No = 36;
const int Layer_No = 40;
void decode_cellid(int cellID,int &layer,int &chip,int &channel){
    layer=cellID/1E5;
	chip=(cellID-layer*1E5)/1E4;
	channel=cellID%100;
	if (channel > channel_No || chip > chip_No || layer > Layer_No || channel < 0 || chip < 0 || layer < 0) {
		std::cout << "Error: cellID out of range: " << cellID << std::endl;
		return;
	}
}
void compare_MIP() {
    TFile* fold = TFile::Open("calibration/mip.root", "READ");
    TFile* fnew = TFile::Open("../AHCAL-analyse-EHN1/run32/MuonADC_offset.root_mip.root", "READ");
    if (!fold || !fnew) {
        std::cerr << "Error opening files!" << std::endl;
        return;
    }
    TTree* told = (TTree*)fold->Get("MIP_Calibration");
    TTree* tnew = (TTree*)fnew->Get("mip");
    if (!told || !tnew) {
        std::cerr << "Error retrieving trees!" << std::endl;
        return;
    }
    const int nChannels = 36*9*40;
    TH2D *hOld = new TH2D("hOld", " MIP Calibration;Layer*Chip;Channel", 9*40, 0, 9*40, 36, 0, 36);
    TH2D *hNew = new TH2D("hNew", "New MIP Calibration;Layer*Chip;Channel", 9*40, 0, 9*40, 36, 0, 36);
    int CellID, Layer, Chip, Channel;
    double MPV;
    int tag;
    told->SetBranchAddress("CellID", &CellID);
    told->SetBranchAddress("MPV", &MPV);
    told->SetBranchAddress("Tag", &tag);
    for (Int_t i = 0; i < told->GetEntries(); i++) {
        told->GetEntry(i);
        // if (tag != 1) continue;
        decode_cellid(CellID, Layer, Chip, Channel);
        hOld->Fill(Layer * 9 + Chip, Channel, MPV);
    }
    tnew->SetBranchAddress("cellid", &CellID);
    tnew->SetBranchAddress("MPV", &MPV);
    int chi2perndf;
    tnew->SetBranchAddress("chi2perndf", &chi2perndf);
    for (Int_t i = 0; i < tnew->GetEntries(); i++) {
        tnew->GetEntry(i);
        // if (chi2perndf > 2) continue;
        decode_cellid(CellID, Layer, Chip, Channel);
        hNew->Fill(Layer * 9 + Chip, Channel, MPV);
    }
    gStyle->SetOptStat(0);
    // gStyle->SetTitleFontSize(0.2);
    // gStyle->SetTitleAlign(23);
    // gStyle->SetTitleX(0.5);
    // gStyle->SetTitleY(0.98);
    // gStyle->SetLabelSize(0.10,"XYZ");
    // gStyle->SetTitleOffset(0.7,"Y");
    TCanvas* c1 = new TCanvas("c1", "MIP Comparison", 8000, 2400);
    c1->Divide(1,4);
    c1->cd(1)->SetTopMargin(0.1);
    hOld->GetZaxis()->SetRangeUser(0,700);
    hOld->Draw("COLZ");
    c1->cd(2)->SetTopMargin(0.1);
    hNew->GetZaxis()->SetRangeUser(0,700);
    hNew->Draw("COLZ");
    c1->cd(3)->SetTopMargin(0.1);
    TH2D* hDiff = (TH2D*)hNew->Clone("hDiff");
    hDiff->SetTitle("Difference (new-old);Layer*Chip;Channel");
    hDiff->Add(hOld, -1);
    hDiff->Draw("COLZ");
    // c1->cd(4);
    TH2D* hDiffAbs = new TH2D("hDiffAbs", "Absolute Difference >50;Layer*Chip;Channel", 9*40, 0, 9*40, 36, 0, 36);
    for (int i=1;i<=hDiff->GetNbinsX();i++){
        for (int j=1;j<=hDiff->GetNbinsY();j++){
            double val=hDiff->GetBinContent(i,j);
            if (std::abs(val)>50){
                // std::cout<<"Large difference at Layer*Chip "<<i<<" Channel "<<j<<" Difference: "<<val<<std::endl;
                hDiffAbs->SetBinContent(i,j,abs(val));
            }
        }
    }
    c1->cd(4)->SetTopMargin(0.1);
    hDiffAbs->Draw("COLZ");
    c1->SaveAs("MIP_Comparison.png");

    fold->Close();
    fnew->Close();
}