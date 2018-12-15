#include"systemc.h"

const double Qmax=2;
const double pi=3.14;
const double r=0.18;
const double g=9.8;
const double p=1;
const double lb=4.1;
const double ub=5.9;

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
wl_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<1999.0;i++)
{
if (true&&true&&wl_w && !wl_r)
{wait(0.008,SC_SEC);
double currentX[1] = {d};
double arguments[1];
double phi[1];
double *k1 = ode1(currentX);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 0.008;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 0.008;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k3[j] * 0.008;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<1; j++){
phi[j] += k4[j] / 6;
}
d=d+phi[0]*0.008;
wait(0,SC_SEC,wl_w.posedge_event());
}
else 
break;
}
if (true&&true&&wl_w && !wl_r)
{wait(0.007999240420758724,SC_SEC);
double currentX[1] = {d};
double arguments[1];
double phi[1];
double *k1 = ode1(currentX);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 0.007999240420758724;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 0.007999240420758724;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k3[j] * 0.007999240420758724;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<1; j++){
phi[j] += k4[j] / 6;
}
d=d+phi[0]*0.007999240420758724;
wait(SC_ZERO_TIME);
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
wl_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<1999.0;i++)
{
if (true&&true&&wl_w && !wl_r)
{wait(0.008,SC_SEC);
double currentX[1] = {d};
double arguments[1];
double phi[1];
double *k1 = ode2(currentX);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 0.008;
phi[j] = k1[j] / 6;
}
double *k2 = ode2(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 0.008;
phi[j] += k2[j] / 3;
}
double *k3 = ode2(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k3[j] * 0.008;
phi[j] += k3[j] / 3;
}
double *k4 = ode2(arguments);
for (int j=0; j<1; j++){
phi[j] += k4[j] / 6;
}
d=d+phi[0]*0.008;
wait(0,SC_SEC,wl_w.posedge_event());
}
else 
break;
}
if (true&&true&&wl_w && !wl_r)
{wait(0.007999240420758724,SC_SEC);
double currentX[1] = {d};
double arguments[1];
double phi[1];
double *k1 = ode2(currentX);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 0.007999240420758724;
phi[j] = k1[j] / 6;
}
double *k2 = ode2(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 0.007999240420758724;
phi[j] += k2[j] / 3;
}
double *k3 = ode2(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k3[j] * 0.007999240420758724;
phi[j] += k3[j] / 3;
}
double *k4 = ode2(arguments);
for (int j=0; j<1; j++){
phi[j] += k4[j] / 6;
}
d=d+phi[0]*0.007999240420758724;
wait(SC_ZERO_TIME);
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
double* ode1(double arguments[]){
double d;
double *temp = new double[1];
d=arguments[0];
temp[0]=Qmax-pi*r*r*sqrt(2*g*d);
return temp;
}
double* ode2(double arguments[]){
double d;
double *temp = new double[1];
d=arguments[0];
temp[0]=-pi*r*r*sqrt(2*g*d);
return temp;
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
sc_start(+16.0,SC_SEC);
for(int j=0;j<1100;j++)
{
cout<<"v: ["<<mytest0.values[j]<<"]"<<endl;
cout<<"d: ["<<mytest1.values[j]<<"]"<<endl;
cout<<"y: ["<<mytest2.values[j]<<"]"<<endl;
cout<<"x: ["<<mytest3.values[j]<<"]"<<endl;
}
return 0;
}
