#include"systemc.h"

const double delay=0.9;

SC_MODULE(singleDDE_02){
sc_out<double> y1;
sc_out<double> y2;

SC_CTOR(singleDDE_02){
SC_THREAD(DDE_02);
}
void DDE_02(void){
double y1_values[36]={0.694193,0.506462,0.403251,0.351880,0.327808,0.316616,0.317074,0.326139,0.340577,0.357655,0.375392,0.393314,0.411236,0.428959,0.446230,0.462783,0.478505,0.493391,0.507470,0.520776,0.533325,0.545138,0.556249,0.566702,0.576543,0.585815,0.594556,0.602801,0.610585,0.617942,0.624903,0.631496,0.637749,0.643684,0.649324,0.654689};
double y2_values[36]={0.511832,0.521001,0.528108,0.533615,0.537884,0.521160,0.491010,0.456008,0.422482,0.393465,0.367264,0.343416,0.321921,0.302868,0.286272,0.271713,0.258789,0.247215,0.236808,0.227454,0.219028,0.211400,0.204455,0.198098,0.192263,0.186891,0.181933,0.177342,0.173076,0.169102,0.165389,0.161913,0.158653,0.155588,0.152701,0.149975};
for (int i=0;i<36.0;i++)
{
if (true&&true)
{
wait(0.225,SC_SEC);
y1=y1_values[i];
y2=y2_values[i];
wait(SC_ZERO_TIME);
}
else 
break;
}
if (true&&true)
{
return;
}
}
};
SC_MODULE(test) {
sc_in<double> s_in;
double min,max;
SC_CTOR(test){
SC_THREAD(update);
dont_initialize();
sensitive<<s_in;
}
void update(){
min=max=s_in;
while(1){
wait();
if (s_in>max) max=s_in;
if (s_in<min) min=s_in;
}
}
};
int sc_main(int argc,char *argv[]){
sc_signal<double> s[2];
singleDDE_02 myinstance("myinstance");
myinstance.y1(s[0]);
myinstance.y2(s[1]);
test mytest0("mytest0");
mytest0.s_in(s[0]);
test mytest1("mytest1");
mytest1.s_in(s[1]);
sc_start(+8.0,SC_SEC);
cout<<"y1: ["<<mytest0.min<<", "<<mytest0.max<<"]"<<endl;
cout<<"y2: ["<<mytest1.min<<", "<<mytest1.max<<"]"<<endl;
return 0;
}
