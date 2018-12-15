#include"systemc.h"

const double Qmax=2;
const double pi=3.14;
const double r=0.18;
const double g=9.8;
const double p=1;
const double lb=4.4;
const double ub=5.6;
const double delay=0.1;
int kk1=0;
int kk2=0;

SC_MODULE(WTS){
sc_out<double> v;
sc_out<double> d;
sc_out<double> y;
sc_out<double> x;
sc_signal<double> wl;
sc_signal<bool> wl_r,wl_w;
sc_event wl_r_done,wl_w_done;
sc_signal<double> cv;
sc_signal<bool> cv_r,cv_w;
sc_event cv_r_done,cv_w_done;

SC_CTOR(WTS){
SC_THREAD(Watertank);
SC_THREAD(Controller);
}
void Watertank(void){
d=4.5;
wait(SC_ZERO_TIME);
cv_r=1;
wait(SC_ZERO_TIME);
if (!cv_w) wait(cv_w.posedge_event());
wait(cv_w_done);
v=cv.read();
wait(SC_ZERO_TIME);
cv_r_done.notify();
cv_r=0;
wait(SC_ZERO_TIME);
wl_w=1;
wait(SC_ZERO_TIME);
if (!wl_r) wait(wl_r.posedge_event());
wl.write(d);
wait(SC_ZERO_TIME);
wl_w_done.notify();
wait(wl_r_done);
wl_w=0;
wait(SC_ZERO_TIME);
while (true)
{
W();
}
}
void W(void){
if (v==1)
{
W1();
}
if (v==0)
{
W2();
}
}
void W1(void){
double d_DDE1_values[200]={4.526114,4.552193,4.578237,4.604247,4.630223,4.656130,4.681969,4.707740,4.733443,4.759079,4.784648,4.810150,4.835586,4.860957,4.886261,4.911500,4.936675,4.961785,4.986831,5.011813,5.036731,5.061586,5.086378,5.111108,5.135775,5.160381,5.184924,5.209407,5.233828,5.258189,5.282489,5.306729,5.330909,5.355029,5.379090,5.403092,5.427036,5.450921,5.474747,5.498516,5.522227,5.545881,5.569477,5.593017,5.616500,5.639927,5.663297,5.686612,5.709871,5.733075,5.756224,5.779317,5.802357,5.825342,5.848272,5.871149,5.893972,5.916742,5.939458,5.962122,5.984733,6.007291,6.029797,6.052251,6.074653,6.097003,6.119302,6.141549,6.163746,6.185892,6.207987,6.230032,6.252027,6.273971,6.295866,6.317712,6.339508,6.361255,6.382952,6.404602,3.454578,3.483597,3.512605,3.541601,3.570585,3.599481,3.628291,3.657014,3.685652,3.714204,3.742671,3.771054,3.799354,3.827571,3.855705,3.883757,3.911728,3.939619,3.967428,3.995159,4.022809,4.050382,4.077875,4.105291,4.132630,4.159892,4.187078,4.214188,4.241222,4.268182,4.295067,4.321878,4.348616,4.375280,4.401872,4.428391,4.454838,4.481214,4.507519,4.533753,4.559917,4.586012,4.612036,4.637992,4.663879,4.689697,4.715448,4.741131,4.766747,4.792296,4.817778,4.843194,4.868545,4.893830,4.919050,4.944205,4.969296,4.994322,5.019285,5.044184,5.069021,5.093794,5.118505,5.143154,5.167741,5.192266,5.216730,5.241133,5.265475,5.289757,5.313979,5.338141,5.362244,5.386288,5.410272,5.434198,5.458065,5.481874,5.505626,5.529320,5.552956,5.576536,5.600058,5.623525,5.646934,5.670288,5.693586,5.716829,5.740016,5.763148,5.786226,5.809249,5.832217,5.855132,5.877993,5.900800,5.923553,5.946254,5.968902,5.991497,6.014039,6.036529,6.058968,6.081354,6.103689,6.125973,6.148205,6.170386,6.192517,6.214597,6.236627,6.258607,6.280536,6.302416,6.324247,6.346028,6.367760,6.389444,6.411078,6.432664};
wl_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<400.0;i++)
{
if (true&&true&&wl_w && !wl_r)
{wait(0.025,SC_SEC);
d=d_DDE1_values[kk1];
kk1++;
wait(0,SC_SEC,wl_w.posedge_event());
}
else 
break;
}
if (!(true&&true)&&wl_w && !wl_r)
{wl_w=0;
wait(SC_ZERO_TIME);
}
if (wl_w && wl_r){
int count=0,a[1],j=-1;
if (wl_w&&wl_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
wl.write(d);
wait(SC_ZERO_TIME);
wl_w_done.notify();
wait(wl_r_done);
wl_w=0;
wait(SC_ZERO_TIME);
wl_w=0;
wait(SC_ZERO_TIME);
W1_1();
break;
}
}
if (true&&true&& wl_w && !wl_r){
return;
}
}
void W1_1(void){
cv_r=1;
wait(SC_ZERO_TIME);
if (!cv_w) wait(cv_w.posedge_event());
wait(cv_w_done);
v=cv.read();
wait(SC_ZERO_TIME);
cv_r_done.notify();
cv_r=0;
wait(SC_ZERO_TIME);
}
void W2(void){
double d_DDE2_values[200]={6.376202,6.347810,6.319425,6.291048,6.262678,6.234372,6.206129,6.177950,6.149835,6.121783,6.093796,6.065871,6.038011,6.010215,5.982482,5.954813,5.927207,5.899666,5.872188,5.844774,5.817424,5.790137,5.762915,5.735756,5.708661,5.681629,5.654662,5.627758,5.600918,5.574141,5.547429,5.520780,5.494195,5.467674,5.441216,5.414823,5.388493,5.362227,5.336024,5.309886,5.283811,5.257800,5.231853,5.205969,5.180150,5.154394,5.128702,5.103074,5.077509,5.052008,5.026571,5.001198,4.975889,4.950644,4.925462,4.900344,4.875290,4.850300,4.825373,4.800510,4.775711,4.750976,4.726305,4.701697,4.677154,4.652674,4.628258,4.603905,4.579617,4.555392,4.531232,4.507135,4.483101,4.459132,4.435226,4.411385,4.387607,4.363893,4.340242,4.316656,4.293133,4.269674,4.246279,4.222948,4.199681,4.176477,4.153338,4.130262,4.107250,4.084302,4.061417,4.038597,4.015840,3.993147,3.970518,3.947953,3.925452,3.903015,3.880641,3.858331,3.836085,3.813903,3.791785,3.769731,3.747740,3.725814,3.703951,3.682152,3.660417,3.638746,3.617138,3.595595,3.574115,3.552700,3.531348,3.510060,3.488836,3.467675,3.446579,3.425547,6.404202,6.375747,6.347300,6.318860,6.290428,6.262059,6.233754,6.205513,6.177335,6.149221,6.121171,6.093184,6.065262,6.037403,6.009608,5.981876,5.954209,5.926605,5.899065,5.871588,5.844176,5.816827,5.789542,5.762320,5.735163,5.708069,5.681039,5.654073,5.627170,5.600332,5.573557,5.546846,5.520198,5.493615,5.467095,5.440639,5.414246,5.387918,5.361653,5.335452,5.309315,5.283242,5.257232,5.231286,5.205404,5.179586,5.153832,5.128141,5.102514,5.076951,5.051452,5.026016,5.000645,4.975337,4.950092,4.924912,4.899796,4.874743,4.849754,4.824829,4.799968,4.775170,4.750436,4.725766,4.701160,4.676618,4.652140,4.627725,4.603374,4.579087,4.554864,4.530704,4.506609,4.482577,4.458609,4.434705,4.410864,4.387088,4.363375,4.339726};
wl_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<400.0;i++)
{
if (true&&true&&wl_w && !wl_r)
{wait(0.025,SC_SEC);
d=d_DDE2_values[kk2];
kk2++;
wait(0,SC_SEC,wl_w.posedge_event());
}
else 
break;
}
if (!(true&&true)&&wl_w && !wl_r)
{wl_w=0;
wait(SC_ZERO_TIME);
}
if (wl_w && wl_r){
int count=0,a[1],j=-1;
if (wl_w&&wl_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
wl.write(d);
wait(SC_ZERO_TIME);
wl_w_done.notify();
wait(wl_r_done);
wl_w=0;
wait(SC_ZERO_TIME);
wl_w=0;
wait(SC_ZERO_TIME);
W1_1();
break;
}
}
if (true&&true&& wl_w && !wl_r){
return;
}
}
void Controller(void){
y=1;
wait(SC_ZERO_TIME);
cv_w=1;
wait(SC_ZERO_TIME);
if (!cv_r) wait(cv_r.posedge_event());
cv.write(y);
wait(SC_ZERO_TIME);
cv_w_done.notify();
wait(cv_r_done);
cv_w=0;
wait(SC_ZERO_TIME);
wl_r=1;
wait(SC_ZERO_TIME);
if (!wl_w) wait(wl_w.posedge_event());
wait(wl_w_done);
x=wl.read();
wait(SC_ZERO_TIME);
wl_r_done.notify();
wl_r=0;
wait(SC_ZERO_TIME);
while (true)
{
C();
}
}
void C(void){
wait(p,SC_SEC);
wl_r=1;
wait(SC_ZERO_TIME);
if (!wl_w) wait(wl_w.posedge_event());
wait(wl_w_done);
x=wl.read();
wait(SC_ZERO_TIME);
wl_r_done.notify();
wl_r=0;
wait(SC_ZERO_TIME);
if (x>=ub)
{
C1();
}
if (x<=lb)
{
C2();
}
cv_w=1;
wait(SC_ZERO_TIME);
if (!cv_r) wait(cv_r.posedge_event());
cv.write(y);
wait(SC_ZERO_TIME);
cv_w_done.notify();
wait(cv_r_done);
cv_w=0;
wait(SC_ZERO_TIME);
}
void C1(void){
y=0;
wait(SC_ZERO_TIME);
}
void C2(void){
y=1;
wait(SC_ZERO_TIME);
}
};
SC_MODULE(test) {
sc_in<double> s_in;
double values[1000];
int i=0;
SC_CTOR(test){
SC_THREAD(update);
dont_initialize();
sensitive<<s_in;
}
void update(){
while(1){
wait();
values[i++]=s_in;

}
}
};
int sc_main(int argc,char *argv[]){
sc_signal<double> s[4];
WTS myinstance("myinstance");
myinstance.v(s[0]);
myinstance.d(s[1]);
myinstance.y(s[2]);
myinstance.x(s[3]);
test mytest0("mytest0");
mytest0.s_in(s[0]);
test mytest1("mytest1");
mytest1.s_in(s[1]);
test mytest2("mytest2");
mytest2.s_in(s[2]);
test mytest3("mytest3");
mytest3.s_in(s[3]);
sc_start(+10.0,SC_SEC);
for(int j=0;j<1100;j++)
{
cout<<"v: ["<<mytest0.values[j]<<"]"<<endl;
cout<<"d: ["<<mytest1.values[j]<<"]"<<endl;
cout<<"y: ["<<mytest2.values[j]<<"]"<<endl;
cout<<"x: ["<<mytest3.values[j]<<"]"<<endl;
}
return 0;
}
