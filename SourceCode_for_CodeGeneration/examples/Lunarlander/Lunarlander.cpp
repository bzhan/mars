#include"systemc.h"

const double gM=1.622;
const double Isp1=2548;
const double Isp2=2842;
const double p=0.128;
const double bound=3000;

SC_MODULE(Slow_ph){
sc_out<double> m;
sc_out<double> v;
sc_out<double> r;
sc_out<double> L_Fc;
sc_out<double> C_m;
sc_out<double> C_v;
sc_out<double> Fc;
sc_signal<double> ch_m;
sc_signal<bool> ch_m_r,ch_m_w;
sc_event ch_m_r_done,ch_m_w_done;
sc_signal<double> ch_v;
sc_signal<bool> ch_v_r,ch_v_w;
sc_event ch_v_r_done,ch_v_w_done;
sc_signal<double> ch_Fc;
sc_signal<bool> ch_Fc_r,ch_Fc_w;
sc_event ch_Fc_r_done,ch_Fc_w_done;

SC_CTOR(Slow_ph){
SC_THREAD(Lander);
SC_THREAD(Controller);
}
void Lander(void){
m=1250;
wait(SC_ZERO_TIME);
v=-2;
wait(SC_ZERO_TIME);
r=30;
wait(SC_ZERO_TIME);
L_Fc=2027.5;
wait(SC_ZERO_TIME);
while (true)
{
P();
}
}
void P(void){
if (L_Fc<=bound)
{
P1();
}
if (L_Fc>bound)
{
P2();
}
}
void P1(void){
ch_m_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<50000.0;i++)
{
if (true&&true&&ch_m_w && !ch_m_r)
{wait(2.0E-4,SC_SEC);
double currentX[4] = {v,m,r,L_Fc};
double arguments[4];
double phi[4];
double *k1 = ode1(currentX);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 2.0E-4;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 2.0E-4;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k3[j] * 2.0E-4;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<4; j++){
phi[j] += k4[j] / 6;
}
v=v+phi[0]*2.0E-4;
m=m+phi[1]*2.0E-4;
r=r+phi[2]*2.0E-4;
L_Fc=L_Fc+phi[3]*2.0E-4;
wait(0,SC_SEC,ch_m_w.posedge_event());
}
else 
break;
}
if (true&&true&&ch_m_w && !ch_m_r)
{wait(2.5262124836444855E-7,SC_SEC);
double currentX[4] = {v,m,r,L_Fc};
double arguments[4];
double phi[4];
double *k1 = ode1(currentX);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 2.5262124836444855E-7;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 2.5262124836444855E-7;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k3[j] * 2.5262124836444855E-7;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<4; j++){
phi[j] += k4[j] / 6;
}
v=v+phi[0]*2.5262124836444855E-7;
m=m+phi[1]*2.5262124836444855E-7;
r=r+phi[2]*2.5262124836444855E-7;
L_Fc=L_Fc+phi[3]*2.5262124836444855E-7;
wait(SC_ZERO_TIME);
}
if (!(true&&true)&&ch_m_w && !ch_m_r)
{ch_m_w=0;
wait(SC_ZERO_TIME);
}
if (ch_m_w && ch_m_r){
int count=0,a[1],j=-1;
if (ch_m_w&&ch_m_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
ch_m.write(m);
wait(SC_ZERO_TIME);
ch_m_w_done.notify();
wait(ch_m_r_done);
ch_m_w=0;
wait(SC_ZERO_TIME);
ch_m_w=0;
wait(SC_ZERO_TIME);
P1_1();
break;
}
}
if (true&&true&& ch_m_w && !ch_m_r){
return;
}
}
void P1_1(void){
ch_v_w=1;
wait(SC_ZERO_TIME);
if (!ch_v_r) wait(ch_v_r.posedge_event());
ch_v.write(v);
wait(SC_ZERO_TIME);
ch_v_w_done.notify();
wait(ch_v_r_done);
ch_v_w=0;
wait(SC_ZERO_TIME);
ch_Fc_r=1;
wait(SC_ZERO_TIME);
if (!ch_Fc_w) wait(ch_Fc_w.posedge_event());
wait(ch_Fc_w_done);
L_Fc=ch_Fc.read();
wait(SC_ZERO_TIME);
ch_Fc_r_done.notify();
ch_Fc_r=0;
wait(SC_ZERO_TIME);
}
void P2(void){
ch_m_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<50000.0;i++)
{
if (true&&true&&ch_m_w && !ch_m_r)
{wait(2.0E-4,SC_SEC);
double currentX[4] = {v,m,r,L_Fc};
double arguments[4];
double phi[4];
double *k1 = ode2(currentX);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 2.0E-4;
phi[j] = k1[j] / 6;
}
double *k2 = ode2(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 2.0E-4;
phi[j] += k2[j] / 3;
}
double *k3 = ode2(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k3[j] * 2.0E-4;
phi[j] += k3[j] / 3;
}
double *k4 = ode2(arguments);
for (int j=0; j<4; j++){
phi[j] += k4[j] / 6;
}
v=v+phi[0]*2.0E-4;
m=m+phi[1]*2.0E-4;
r=r+phi[2]*2.0E-4;
L_Fc=L_Fc+phi[3]*2.0E-4;
wait(0,SC_SEC,ch_m_w.posedge_event());
}
else 
break;
}
if (true&&true&&ch_m_w && !ch_m_r)
{wait(2.5262124836444855E-7,SC_SEC);
double currentX[4] = {v,m,r,L_Fc};
double arguments[4];
double phi[4];
double *k1 = ode2(currentX);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 2.5262124836444855E-7;
phi[j] = k1[j] / 6;
}
double *k2 = ode2(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 2.5262124836444855E-7;
phi[j] += k2[j] / 3;
}
double *k3 = ode2(arguments);
for (int j=0; j<4; j++){
arguments[j] = currentX[j] + k3[j] * 2.5262124836444855E-7;
phi[j] += k3[j] / 3;
}
double *k4 = ode2(arguments);
for (int j=0; j<4; j++){
phi[j] += k4[j] / 6;
}
v=v+phi[0]*2.5262124836444855E-7;
m=m+phi[1]*2.5262124836444855E-7;
r=r+phi[2]*2.5262124836444855E-7;
L_Fc=L_Fc+phi[3]*2.5262124836444855E-7;
wait(SC_ZERO_TIME);
}
if (!(true&&true)&&ch_m_w && !ch_m_r)
{ch_m_w=0;
wait(SC_ZERO_TIME);
}
if (ch_m_w && ch_m_r){
int count=0,a[1],j=-1;
if (ch_m_w&&ch_m_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
ch_m.write(m);
wait(SC_ZERO_TIME);
ch_m_w_done.notify();
wait(ch_m_r_done);
ch_m_w=0;
wait(SC_ZERO_TIME);
ch_m_w=0;
wait(SC_ZERO_TIME);
P1_1();
break;
}
}
if (true&&true&& ch_m_w && !ch_m_r){
return;
}
}
void Controller(void){
Fc=2027.5;
wait(SC_ZERO_TIME);
while (true)
{
C();
}
}
void C(void){
wait(p,SC_SEC);
ch_m_r=1;
wait(SC_ZERO_TIME);
if (!ch_m_w) wait(ch_m_w.posedge_event());
wait(ch_m_w_done);
C_m=ch_m.read();
wait(SC_ZERO_TIME);
ch_m_r_done.notify();
ch_m_r=0;
wait(SC_ZERO_TIME);
ch_v_r=1;
wait(SC_ZERO_TIME);
if (!ch_v_w) wait(ch_v_w.posedge_event());
wait(ch_v_w_done);
C_v=ch_v.read();
wait(SC_ZERO_TIME);
ch_v_r_done.notify();
ch_v_r=0;
wait(SC_ZERO_TIME);
Fc=C_m*gM-0.01*(Fc-C_m*gM)-0.6*(C_v+2)*C_m;
wait(SC_ZERO_TIME);
ch_Fc_w=1;
wait(SC_ZERO_TIME);
if (!ch_Fc_r) wait(ch_Fc_r.posedge_event());
ch_Fc.write(Fc);
wait(SC_ZERO_TIME);
ch_Fc_w_done.notify();
wait(ch_Fc_r_done);
ch_Fc_w=0;
wait(SC_ZERO_TIME);
}
double* ode1(double arguments[]){
double v,m,r,L_Fc;
double *temp = new double[4];
v=arguments[0];m=arguments[1];r=arguments[2];L_Fc=arguments[3];
temp[0]=(L_Fc/m)-gM;temp[1]=-L_Fc/Isp1;temp[2]=v;temp[3]=0;
return temp;
}
double* ode2(double arguments[]){
double v,m,r,L_Fc;
double *temp = new double[4];
v=arguments[0];m=arguments[1];r=arguments[2];L_Fc=arguments[3];
temp[0]=(L_Fc/m)-gM;temp[1]=-L_Fc/Isp2;temp[2]=v;temp[3]=0;
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
sc_signal<double> s[7];
Slow_ph myinstance("myinstance");
myinstance.m(s[0]);
myinstance.v(s[1]);
myinstance.r(s[2]);
myinstance.L_Fc(s[3]);
myinstance.C_m(s[4]);
myinstance.C_v(s[5]);
myinstance.Fc(s[6]);
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
sc_start(+10.0,SC_SEC);
cout<<"m: ["<<mytest0.min<<", "<<mytest0.max<<"]"<<endl;
cout<<"v: ["<<mytest1.min<<", "<<mytest1.max<<"]"<<endl;
cout<<"r: ["<<mytest2.min<<", "<<mytest2.max<<"]"<<endl;
cout<<"L_Fc: ["<<mytest3.min<<", "<<mytest3.max<<"]"<<endl;
cout<<"C_m: ["<<mytest4.min<<", "<<mytest4.max<<"]"<<endl;
cout<<"C_v: ["<<mytest5.min<<", "<<mytest5.max<<"]"<<endl;
cout<<"Fc: ["<<mytest6.min<<", "<<mytest6.max<<"]"<<endl;
return 0;
}
