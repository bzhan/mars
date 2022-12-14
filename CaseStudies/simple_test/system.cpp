#include"systemc.h"


SC_MODULE(P){
sc_out<double> plant_1;
sc_out<double> control_1;
sc_out<double> plant_1_1;
sc_out<double> control_1_0;
sc_signal<double> Ch_plant_1_1;
sc_signal<bool> Ch_plant_1_1_r,Ch_plant_1_1_w;
sc_event Ch_plant_1_1_r_done,Ch_plant_1_1_w_done;
sc_signal<double> Ch_control_1_0;
sc_signal<bool> Ch_control_1_0_r,Ch_control_1_0_w;
sc_event Ch_control_1_0_r_done,Ch_control_1_0_w_done;

SC_CTOR(P){
SC_THREAD(PC1);
SC_THREAD(PD1);
}
void PC1_1(void){
plant_1=1;
wait(SC_ZERO_TIME);
}
void commI1(void){
Ch_control_1_0_r=1;
wait(SC_ZERO_TIME);
if (!Ch_control_1_0_w) wait(Ch_control_1_0_w.posedge_event());
wait(Ch_control_1_0_w_done);
control_1_0=Ch_control_1_0.read();
wait(SC_ZERO_TIME);
Ch_control_1_0_r_done.notify();
Ch_control_1_0_r=0;
wait(SC_ZERO_TIME);
Ch_plant_1_1_w=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_1_1_r) wait(Ch_plant_1_1_r.posedge_event());
Ch_plant_1_1.write(plant_1);
wait(SC_ZERO_TIME);
Ch_plant_1_1_w_done.notify();
wait(Ch_plant_1_1_r_done);
Ch_plant_1_1_w=0;
wait(SC_ZERO_TIME);
}
void interrupt_2_proc(void){
Ch_control_1_0_r=1;
wait(SC_ZERO_TIME);
if (!Ch_control_1_0_w) wait(Ch_control_1_0_w.posedge_event());
wait(Ch_control_1_0_w_done);
control_1_0=Ch_control_1_0.read();
wait(SC_ZERO_TIME);
Ch_control_1_0_r_done.notify();
Ch_control_1_0_r=0;
wait(SC_ZERO_TIME);
}
void domain_2_proc(void){
Ch_plant_1_1_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<284.0;i++)
{
if (true&&true&&Ch_plant_1_1_w && !Ch_plant_1_1_r)
{wait(0.7,SC_SEC);
double currentX[1] = {plant_1};
double arguments[1];
double phi[1];
double *k1 = ode1(currentX);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 0.7;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 0.7;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k3[j] * 0.7;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<1; j++){
phi[j] += k4[j] / 6;
}
plant_1=plant_1+phi[0]*0.7;
wait(0,SC_SEC,Ch_plant_1_1_w.posedge_event());
}
else 
break;
}
if (true&&true&&Ch_plant_1_1_w && !Ch_plant_1_1_r)
{wait(0.20000338554382324,SC_SEC);
double currentX[1] = {plant_1};
double arguments[1];
double phi[1];
double *k1 = ode1(currentX);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k1[j] / 2 * 0.20000338554382324;
phi[j] = k1[j] / 6;
}
double *k2 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k2[j] / 2 * 0.20000338554382324;
phi[j] += k2[j] / 3;
}
double *k3 = ode1(arguments);
for (int j=0; j<1; j++){
arguments[j] = currentX[j] + k3[j] * 0.20000338554382324;
phi[j] += k3[j] / 3;
}
double *k4 = ode1(arguments);
for (int j=0; j<1; j++){
phi[j] += k4[j] / 6;
}
plant_1=plant_1+phi[0]*0.20000338554382324;
wait(SC_ZERO_TIME);
}
if (!(true&&true)&&Ch_plant_1_1_w && !Ch_plant_1_1_r)
{Ch_plant_1_1_w=0;
wait(SC_ZERO_TIME);
}
if (Ch_plant_1_1_w && Ch_plant_1_1_r){
int count=0,a[1],j=-1;
if (Ch_plant_1_1_w&&Ch_plant_1_1_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
Ch_plant_1_1.write(plant_1);
wait(SC_ZERO_TIME);
Ch_plant_1_1_w_done.notify();
wait(Ch_plant_1_1_r_done);
Ch_plant_1_1_w=0;
wait(SC_ZERO_TIME);
Ch_plant_1_1_w=0;
wait(SC_ZERO_TIME);
interrupt_2_proc();
break;
}
}
if (true&&true&& Ch_plant_1_1_w && !Ch_plant_1_1_r){
return;
}
}
void PC1_2(void){
if ((true))
{
domain_2_proc();
}
}
void PC1_init(void){
PC1_1();
commI1();
}
void PC1_rep(void){
PC1_2();
}
void PC1(void){
PC1_init();
while (true)
{
PC1_rep();
}
}
void PD1_1(void){
control_1=(1);
wait(SC_ZERO_TIME);
}
void PD1_2(void){
Ch_control_1_0_w=1;
wait(SC_ZERO_TIME);
if (!Ch_control_1_0_r) wait(Ch_control_1_0_r.posedge_event());
Ch_control_1_0.write(control_1);
wait(SC_ZERO_TIME);
Ch_control_1_0_w_done.notify();
wait(Ch_control_1_0_r_done);
Ch_control_1_0_w=0;
wait(SC_ZERO_TIME);
Ch_plant_1_1_r=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_1_1_w) wait(Ch_plant_1_1_w.posedge_event());
wait(Ch_plant_1_1_w_done);
plant_1_1=Ch_plant_1_1.read();
wait(SC_ZERO_TIME);
Ch_plant_1_1_r_done.notify();
Ch_plant_1_1_r=0;
wait(SC_ZERO_TIME);
}
void PD1_3(void){
control_1=sqrt(abs(plant_1_1-(2)));
wait(SC_ZERO_TIME);
}
void PD1_4(void){
wait(1,SC_SEC);
}
void PD1_5(void){
Ch_plant_1_1_r=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_1_1_w) wait(Ch_plant_1_1_w.posedge_event());
wait(Ch_plant_1_1_w_done);
plant_1_1=Ch_plant_1_1.read();
wait(SC_ZERO_TIME);
Ch_plant_1_1_r_done.notify();
Ch_plant_1_1_r=0;
wait(SC_ZERO_TIME);
}
void PD1_6(void){
control_1=sqrt(abs(plant_1_1-(2)));
wait(SC_ZERO_TIME);
}
void PD1_7(void){
Ch_control_1_0_w=1;
wait(SC_ZERO_TIME);
if (!Ch_control_1_0_r) wait(Ch_control_1_0_r.posedge_event());
Ch_control_1_0.write(control_1);
wait(SC_ZERO_TIME);
Ch_control_1_0_w_done.notify();
wait(Ch_control_1_0_r_done);
Ch_control_1_0_w=0;
wait(SC_ZERO_TIME);
}
void PD1_init1(void){
PD1_1();
}
void PD1_init2(void){
PD1_2();
}
void PD1_init3(void){
PD1_3();
}
void PD1_init(void){
PD1_init1();
PD1_init2();
PD1_init3();
}
void PD1_rep1(void){
PD1_4();
}
void PD1_rep2(void){
PD1_5();
}
void PD1_rep3(void){
PD1_6();
}
void PD1_rep4(void){
PD1_7();
}
void PD1_rep(void){
PD1_rep1();
PD1_rep2();
PD1_rep3();
PD1_rep4();
}
void PD1(void){
PD1_init();
while (true)
{
PD1_rep();
}
}
double* ode1(double arguments[]){
double plant_1;
double *temp = new double[1];
plant_1=arguments[0];
temp[0]=sqrt(control_1_0+(5));
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
sc_signal<double> s[4];
P myinstance("myinstance");
myinstance.plant_1(s[0]);
myinstance.control_1(s[1]);
myinstance.plant_1_1(s[2]);
myinstance.control_1_0(s[3]);
test mytest0("mytest0");
mytest0.s_in(s[0]);
test mytest1("mytest1");
mytest1.s_in(s[1]);
test mytest2("mytest2");
mytest2.s_in(s[2]);
test mytest3("mytest3");
mytest3.s_in(s[3]);
sc_start(+199.0,SC_SEC);
cout<<"plant_1: ["<<mytest0.min<<", "<<mytest0.max<<"]"<<endl;
cout<<"control_1: ["<<mytest1.min<<", "<<mytest1.max<<"]"<<endl;
cout<<"plant_1_1: ["<<mytest2.min<<", "<<mytest2.max<<"]"<<endl;
cout<<"control_1_0: ["<<mytest3.min<<", "<<mytest3.max<<"]"<<endl;
return 0;
}
