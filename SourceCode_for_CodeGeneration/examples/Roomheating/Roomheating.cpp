#include"systemc.h"

const double u=4;
const double p=0.1;
const double on1=10;
const double on2=10;
const double off1=12;
const double off2=12;
const double get1=8;
const double get2=8;
const double diff1=0.5;
const double diff2=0.5;

SC_MODULE(RH){
sc_out<double> x1;
sc_out<double> x2;
sc_out<double> R_h1;
sc_out<double> R_h2;
sc_out<double> C_x1;
sc_out<double> C_x2;
sc_out<double> h1;
sc_out<double> h2;
sc_out<double> owner;
sc_signal<double> ch_x1;
sc_signal<bool> ch_x1_r,ch_x1_w;
sc_event ch_x1_r_done,ch_x1_w_done;
sc_signal<double> ch_x2;
sc_signal<bool> ch_x2_r,ch_x2_w;
sc_event ch_x2_r_done,ch_x2_w_done;
sc_signal<double> ch_h1;
sc_signal<bool> ch_h1_r,ch_h1_w;
sc_event ch_h1_r_done,ch_h1_w_done;
sc_signal<double> ch_h2;
sc_signal<bool> ch_h2_r,ch_h2_w;
sc_event ch_h2_r_done,ch_h2_w_done;

SC_CTOR(RH){
SC_THREAD(Room);
SC_THREAD(Controller);
}
void Room(void){
x1=10;
wait(SC_ZERO_TIME);
x2=10;
wait(SC_ZERO_TIME);
R_h1=1;
wait(SC_ZERO_TIME);
R_h2=0;
wait(SC_ZERO_TIME);
while (true)
{
R();
}
}
void R(void){
ch_x1_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<25000.0;i++)
{
if (true&&true&&ch_x1_w && !ch_x1_r)
{wait(2.0E-4,SC_SEC);
double currentX[2] = {x1,x2};
double arguments[2];
double phi[2];
double *k1 = ode1(currentX);
for (int j=0; j<2; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 2.0E-4;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<2; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 2.0E-4;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<2; j++){
arguments[j] = currentX[j] + k3[j] * 2.0E-4;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<2; j++){
phi[j] += k4[j] / 6;
}
x1=x1+phi[0]*2.0E-4;
x2=x2+phi[1]*2.0E-4;
wait(0,SC_SEC,ch_x1_w.posedge_event());
}
else 
break;
}
if (true&&true&&ch_x1_w && !ch_x1_r)
{wait(1.2631062418222427E-7,SC_SEC);
double currentX[2] = {x1,x2};
double arguments[2];
double phi[2];
double *k1 = ode1(currentX);
for (int j=0; j<2; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 1.2631062418222427E-7;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<2; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 1.2631062418222427E-7;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<2; j++){
arguments[j] = currentX[j] + k3[j] * 1.2631062418222427E-7;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<2; j++){
phi[j] += k4[j] / 6;
}
x1=x1+phi[0]*1.2631062418222427E-7;
x2=x2+phi[1]*1.2631062418222427E-7;
wait(SC_ZERO_TIME);
}
if (!(true&&true)&&ch_x1_w && !ch_x1_r)
{ch_x1_w=0;
wait(SC_ZERO_TIME);
}
if (ch_x1_w && ch_x1_r){
int count=0,a[1],j=-1;
if (ch_x1_w&&ch_x1_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
ch_x1.write(x1);
wait(SC_ZERO_TIME);
ch_x1_w_done.notify();
wait(ch_x1_r_done);
ch_x1_w=0;
wait(SC_ZERO_TIME);
ch_x1_w=0;
wait(SC_ZERO_TIME);
R_1();
break;
}
}
if (true&&true&& ch_x1_w && !ch_x1_r){
return;
}
}
void R_1(void){
ch_x2_w=1;
wait(SC_ZERO_TIME);
if (!ch_x2_r) wait(ch_x2_r.posedge_event());
ch_x2.write(x2);
wait(SC_ZERO_TIME);
ch_x2_w_done.notify();
wait(ch_x2_r_done);
ch_x2_w=0;
wait(SC_ZERO_TIME);
ch_h1_r=1;
wait(SC_ZERO_TIME);
if (!ch_h1_w) wait(ch_h1_w.posedge_event());
wait(ch_h1_w_done);
R_h1=ch_h1.read();
wait(SC_ZERO_TIME);
ch_h1_r_done.notify();
ch_h1_r=0;
wait(SC_ZERO_TIME);
ch_h2_r=1;
wait(SC_ZERO_TIME);
if (!ch_h2_w) wait(ch_h2_w.posedge_event());
wait(ch_h2_w_done);
R_h2=ch_h2.read();
wait(SC_ZERO_TIME);
ch_h2_r_done.notify();
ch_h2_r=0;
wait(SC_ZERO_TIME);
}
void Controller(void){
owner=1;
wait(SC_ZERO_TIME);
h1=1;
wait(SC_ZERO_TIME);
h2=0;
wait(SC_ZERO_TIME);
while (true)
{
C();
}
}
void C(void){
wait(p,SC_SEC);
ch_x1_r=1;
wait(SC_ZERO_TIME);
if (!ch_x1_w) wait(ch_x1_w.posedge_event());
wait(ch_x1_w_done);
C_x1=ch_x1.read();
wait(SC_ZERO_TIME);
ch_x1_r_done.notify();
ch_x1_r=0;
wait(SC_ZERO_TIME);
ch_x2_r=1;
wait(SC_ZERO_TIME);
if (!ch_x2_w) wait(ch_x2_w.posedge_event());
wait(ch_x2_w_done);
C_x2=ch_x2.read();
wait(SC_ZERO_TIME);
ch_x2_r_done.notify();
ch_x2_r=0;
wait(SC_ZERO_TIME);
if (owner==1&&C_x2<=get2&&(C_x1-C_x2)>=diff2)
{
C_1();
}
if (owner==2&&C_x1<=get1&&(C_x2-C_x1)>=diff1)
{
C_2();
}
if (owner==2&&C_x2<=on2)
{
C_3();
}
if (owner==1&&C_x1<=on1)
{
C_4();
}
if (C_x1>=off1)
{
C_5();
}
if (C_x2>=off2)
{
C_6();
}
ch_h1_w=1;
wait(SC_ZERO_TIME);
if (!ch_h1_r) wait(ch_h1_r.posedge_event());
ch_h1.write(h1);
wait(SC_ZERO_TIME);
ch_h1_w_done.notify();
wait(ch_h1_r_done);
ch_h1_w=0;
wait(SC_ZERO_TIME);
ch_h2_w=1;
wait(SC_ZERO_TIME);
if (!ch_h2_r) wait(ch_h2_r.posedge_event());
ch_h2.write(h2);
wait(SC_ZERO_TIME);
ch_h2_w_done.notify();
wait(ch_h2_r_done);
ch_h2_w=0;
wait(SC_ZERO_TIME);
}
void C_1(void){
owner=2;
wait(SC_ZERO_TIME);
h1=0;
wait(SC_ZERO_TIME);
h2=1;
wait(SC_ZERO_TIME);
}
void C_2(void){
owner=1;
wait(SC_ZERO_TIME);
h1=1;
wait(SC_ZERO_TIME);
h2=0;
wait(SC_ZERO_TIME);
}
void C_3(void){
h1=0;
wait(SC_ZERO_TIME);
h2=1;
wait(SC_ZERO_TIME);
}
void C_4(void){
h1=1;
wait(SC_ZERO_TIME);
h2=0;
wait(SC_ZERO_TIME);
}
void C_5(void){
h1=0;
wait(SC_ZERO_TIME);
}
void C_6(void){
h2=0;
wait(SC_ZERO_TIME);
}
double* ode1(double arguments[]){
double x1,x2;
double *temp = new double[2];
x1=arguments[0];x2=arguments[1];
temp[0]=0.25*x2-0.45*x1+0.2*u+5*R_h1;temp[1]=0.25*x1-0.65*x2+0.15*u+5*R_h2;
return temp;
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
sc_signal<double> s[9];
RH myinstance("myinstance");
myinstance.x1(s[0]);
myinstance.x2(s[1]);
myinstance.R_h1(s[2]);
myinstance.R_h2(s[3]);
myinstance.C_x1(s[4]);
myinstance.C_x2(s[5]);
myinstance.h1(s[6]);
myinstance.h2(s[7]);
myinstance.owner(s[8]);
test mytest0("mytest0");
mytest0.s_in(s[0]);
test mytest1("mytest1");
mytest1.s_in(s[1]);
test mytest2("mytest2");
mytest2.s_in(s[2]);
test mytest3("mytest3");
mytest3.s_in(s[3]);
test mytest4("mytest4");
mytest4.s_in(s[4]);
test mytest5("mytest5");
mytest5.s_in(s[5]);
test mytest6("mytest6");
mytest6.s_in(s[6]);
test mytest7("mytest7");
mytest7.s_in(s[7]);
test mytest8("mytest8");
mytest8.s_in(s[8]);
sc_start(+5.0,SC_SEC);
cout<<"x1: ["<<mytest0.min<<", "<<mytest0.max<<"]"<<endl;
cout<<"x2: ["<<mytest1.min<<", "<<mytest1.max<<"]"<<endl;
cout<<"R_h1: ["<<mytest2.min<<", "<<mytest2.max<<"]"<<endl;
cout<<"R_h2: ["<<mytest3.min<<", "<<mytest3.max<<"]"<<endl;
cout<<"C_x1: ["<<mytest4.min<<", "<<mytest4.max<<"]"<<endl;
cout<<"C_x2: ["<<mytest5.min<<", "<<mytest5.max<<"]"<<endl;
cout<<"h1: ["<<mytest6.min<<", "<<mytest6.max<<"]"<<endl;
cout<<"h2: ["<<mytest7.min<<", "<<mytest7.max<<"]"<<endl;
cout<<"owner: ["<<mytest8.min<<", "<<mytest8.max<<"]"<<endl;
return 0;
}
