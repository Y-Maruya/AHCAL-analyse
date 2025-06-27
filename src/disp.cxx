#include "TFile.h"
#include "TTree.h"
#include "TH3D.h"
#include "TCanvas.h"
#include "TStyle.h"
#include "TApplication.h"
#include "TAxis.h"
#include <string>
#include <iostream>
#include "TSystem.h"
#include "TView.h"
#include "Global.h"
#include <vector>
using namespace std;
const int cchannel[6][6] = {{2, 1, 0, 11, 12, 15},
								{3, 4, 5, 10, 13, 16},
								{6, 7, 8, 9, 14, 17},
								{29, 28, 27, 26, 21, 18},
								{32, 31, 30, 25, 22, 19},
								{35, 34, 33, 24, 23, 20}};
double MIP_E=0.461;
int main(int argc,char* argv[]){
	string filename=argv[1];
	string nentries=argv[2];
	TApplication theApp("app",&argc,argv);
	TFile* fin=TFile::Open(TString(filename),"READ");
	if(!fin){
		cout<<"can not open "<<filename<<endl;
		return -1;

	}
	int n=stoi(nentries);
	TTree* tin=(TTree*)fin->Get("EventTree");
	vector<double> *Hit_Energy=0;
	vector<int> *cellid=0;
	vector<double> *Hit_X=0;
	vector<double> *Hit_Y=0;
	vector<double> *Hit_Z=0;
	// tin->SetBranchAddress("CellID",&cellid);
	tin->SetBranchAddress("Hit_Energy",&Hit_Energy);
	tin->SetBranchAddress("Hit_X",&Hit_X);
	tin->SetBranchAddress("Hit_Y",&Hit_Y);
	tin->SetBranchAddress("Hit_Z",&Hit_Z);

	TH3D* h_display=new TH3D("display","display",400,0,1200,18,-360,360,18,-360,360);
	h_display->GetXaxis()->SetRangeUser(0,800);
	// h_display->GetYaxis()->SetRangeUser(-120,120);
	// h_display->GetZaxis()->SetRangeUser(-120,120);
	TCanvas *c = new TCanvas("c", "c",48,130,1000,723);
	gStyle->SetOptStat(0);
	// c->SetHighLightColor(2);
	// c->Range(-1.020015,-0.8450986,1.020015,0.8450986);
	// TView *view1 = TView::CreateView(1);
	// view1->SetRange(0,0,0,5,5,4);
	// c->SetFillColor(0);
	// c->SetBorderMode(0);
	// c->SetBorderSize(2);
	// c->SetTheta(7.278371);
	// c->SetPhi(43.0265);
	// c->SetFrameBorderMode(0);
	// gStyle->SetCanvasPreferGL(1);
	// h_display->GetXaxis()->SetNdivisions(40);
	// h_display->GetYaxis()->SetNdivisions(18);
	// h_display->GetZaxis()->SetNdivisions(18);
	bool flag=1;
	string tmp="";
	while(flag){
		tin->GetEntry(n);
		h_display->SetTitle("entries_"+TString(nentries));
		h_display->Reset();
		for(int i=0;i<Hit_Energy->size();i++){
			// if(Hit_Energy->at(i)>0.5*MIP_E)
			// {
				double e=Hit_Energy->at(i);
				// e=log(e+1)+10;
				h_display->Fill(Hit_Z->at(i),Hit_X->at(i),Hit_Y->at(i),e);
			// }
		}
		// h_display->SetMinimum(20);
		h_display->Draw("box2");
		c->Update();
		c->Modified();
		do{
			cout<<"next display entry no('q' for quit):"<<endl;
			cin>>tmp;
			if(tmp=="q"){
				flag=0;
				break;
			}
			else{
				try{
					n=stoi(tmp);
				}
				catch(std::invalid_argument){
					cout<<"wrong input!!!"<<endl;
				}
			}
		}while(tmp==nentries);
		nentries=tmp;
		// cout << nentries << endl;
	}
	return 1;	
}
