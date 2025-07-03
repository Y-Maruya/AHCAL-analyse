#ifndef GLOBAL_HH
#define GLOBAL_HH

extern int int_tmp;
extern char char_tmp[200];
const int channel_FEE = 73;//(36charges+36times + BCIDs )*16column+ ChipID
const int cell_SP = 16;
const int chip_No = 9;
const int channel_No = 36;
const int Layer_No = 40;
const double _Pos_X[channel_No]={100.2411,100.2411,100.2411,59.94146,59.94146,59.94146,19.64182,19.64182,19.64182,19.64182,59.94146,100.2411,100.2411,59.94146,19.64182,100.2411,59.94146,19.64182,-20.65782,-60.95746,-101.2571,-20.65782,-60.95746,-101.2571,-101.2571,-60.95746,-20.65782,-20.65782,-20.65782,-20.65782,-60.95746,-60.95746,-60.95746,-101.2571,-101.2571,-101.2571};
const double _Pos_Y[channel_No]={141.04874,181.34838,221.64802,141.04874,181.34838,221.64802,141.04874,181.34838,221.64802,261.94766,261.94766,261.94766,302.2473,302.2473,302.2473,342.54694,342.54694,342.54694,342.54694,342.54694,342.54694,302.2473,302.2473,302.2473,261.94766,261.94766,261.94766,221.64802,181.34838,141.04874,221.64802,181.34838,141.04874,221.64802,181.34838,141.04874};
const int _Channel[6][6]={  { 0, 1, 2,11,12,15},
							{ 3, 4, 5,10,13,16},
							{ 6, 7, 8, 9,14,17},
							{29,28,27,26,21,18},
							{32,31,30,25,22,19},
							{35,34,33,24,23,20}};
const int _Chip[3][3]={ {2,1,0},
						{5,4,3},
						{8,7,6}};
const double chip_dis_X=239.3;
const double chip_dis_Y=241.8;
const double HBU_X=239.3;
const double HBU_Y=725.4; 
inline void decode_cellid(int cellID,int &layer,int &chip,int &channel){
    layer=cellID/1E5;
	chip=(cellID-layer*1E5)/1E4;
	channel=cellID%100;
	if (channel > channel_No || chip > chip_No || layer > Layer_No || channel < 0 || chip < 0 || layer < 0) {
		std::cout << "Error: cellID out of range: " << cellID << std::endl;
		return;
	}
}
inline void inverse(double x,double y,int &chip,int &channel){
	int i=x/40.3+9;
	int j=-y/40.3+9;
	chip=_Chip[j/6][i/6];
	channel=_Channel[j%6][i%6];
	if(chip%3!=0){
		if(channel==2)channel=0;
		else if(channel==0)channel=2;
		if(channel==33)channel=35;
		else if(channel==35)channel=33;
	}
}
inline double Pos_X(int channel_ID,int chip_ID,int HBU_ID=0){
	HBU_ID=chip_ID/3;
	chip_ID=chip_ID%3;
	if(chip_ID!=0){
		if(channel_ID==2)channel_ID=0;
		else if(channel_ID==0)channel_ID=2;
		if(channel_ID==33)channel_ID=35;
		else if(channel_ID==35)channel_ID=33;
	}
	return (_Pos_Y[channel_ID]-chip_ID*chip_dis_Y);
}
inline double Pos_X_1(int cellID){
	int channel=0,chip=0,layer=0;
	decode_cellid(cellID,layer,chip,channel);
	return Pos_X(channel,chip);
}
inline double Pos_Y(int channel_ID,int chip_ID,int HBU_ID=0){
	HBU_ID=chip_ID/3;
	return -(-_Pos_X[channel_ID]+(HBU_ID-1)*HBU_X);
}
inline double Pos_Y_1(int cellID){
	int channel=0,chip=0,layer=0;
	decode_cellid(cellID,layer,chip,channel);
	return Pos_Y(channel,chip);
}

#endif