#include"systemc.h"


SC_MODULE(P){
sc_out<double> plant_v1_1;
sc_out<double> plant_m1_1;
sc_out<double> control_1;
sc_out<double> plant_r1_1;
sc_out<double> plant_v1_1_1;
sc_out<double> plant_m1_1_1;
sc_out<double> control_1_0;
sc_signal<double> Ch_plant_v1_1_1;
sc_signal<bool> Ch_plant_v1_1_1_r,Ch_plant_v1_1_1_w;
sc_event Ch_plant_v1_1_1_r_done,Ch_plant_v1_1_1_w_done;
sc_signal<double> Ch_plant_m1_1_1;
sc_signal<bool> Ch_plant_m1_1_1_r,Ch_plant_m1_1_1_w;
sc_event Ch_plant_m1_1_1_r_done,Ch_plant_m1_1_1_w_done;
sc_signal<double> Ch_control_1_0;
sc_signal<bool> Ch_control_1_0_r,Ch_control_1_0_w;
sc_event Ch_control_1_0_r_done,Ch_control_1_0_w_done;

SC_CTOR(P){
SC_THREAD(PC1);
SC_THREAD(PD1);
}
void PC1_1(void){
plant_v1_1=-2;
wait(SC_ZERO_TIME);
plant_m1_1=1250;
wait(SC_ZERO_TIME);
plant_r1_1=30;
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
Ch_plant_m1_1_1_w=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_m1_1_1_r) wait(Ch_plant_m1_1_1_r.posedge_event());
Ch_plant_m1_1_1.write(plant_m1_1);
wait(SC_ZERO_TIME);
Ch_plant_m1_1_1_w_done.notify();
wait(Ch_plant_m1_1_1_r_done);
Ch_plant_m1_1_1_w=0;
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_w=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_v1_1_1_r) wait(Ch_plant_v1_1_1_r.posedge_event());
Ch_plant_v1_1_1.write(plant_v1_1);
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_w_done.notify();
wait(Ch_plant_v1_1_1_r_done);
Ch_plant_v1_1_1_w=0;
wait(SC_ZERO_TIME);
}
void interrupt_3_proc(void){
Ch_plant_v1_1_1_w=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_v1_1_1_r) wait(Ch_plant_v1_1_1_r.posedge_event());
Ch_plant_v1_1_1.write(plant_v1_1);
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_w_done.notify();
wait(Ch_plant_v1_1_1_r_done);
Ch_plant_v1_1_1_w=0;
wait(SC_ZERO_TIME);
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
void domain_3_proc(void){
Ch_plant_m1_1_1_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<5000.0;i++)
{
if (true&&Ch_plant_m1_1_1_w && !Ch_plant_m1_1_1_r)
{plant_v1_1=plant_v1_1+((control_1_0/plant_m1_1)-(1.622))*0.002;
plant_m1_1=plant_m1_1+(-(control_1_0/(2548)))*0.002;
plant_r1_1=plant_r1_1+(plant_v1_1)*0.002;
wait(0.002,SC_SEC);wait(0,SC_SEC,Ch_plant_m1_1_1_w.posedge_event());
}
else 
break;
}
if (!true&&Ch_plant_m1_1_1_w && !Ch_plant_m1_1_1_r)
{Ch_plant_m1_1_1_w=0;
wait(SC_ZERO_TIME);
}
if (Ch_plant_m1_1_1_w && Ch_plant_m1_1_1_r){
int count=0,a[1],j=-1;
if (Ch_plant_m1_1_1_w&&Ch_plant_m1_1_1_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
Ch_plant_m1_1_1.write(plant_m1_1);
wait(SC_ZERO_TIME);
Ch_plant_m1_1_1_w_done.notify();
wait(Ch_plant_m1_1_1_r_done);
Ch_plant_m1_1_1_w=0;
wait(SC_ZERO_TIME);
Ch_plant_m1_1_1_w=0;
wait(SC_ZERO_TIME);
interrupt_3_proc();
break;
}
}
if (true&& Ch_plant_m1_1_1_w && !Ch_plant_m1_1_1_r){
plant_v1_1=0.0;
plant_m1_1=0.0;
plant_r1_1=0.0;
wait(SC_ZERO_TIME);
return;
}
}
void PC1_2(void){
if (((control_1_0>(3000))))
{
domain_3_proc();
}
}
void interrupt_4_proc(void){
Ch_plant_v1_1_1_w=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_v1_1_1_r) wait(Ch_plant_v1_1_1_r.posedge_event());
Ch_plant_v1_1_1.write(plant_v1_1);
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_w_done.notify();
wait(Ch_plant_v1_1_1_r_done);
Ch_plant_v1_1_1_w=0;
wait(SC_ZERO_TIME);
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
void domain_4_proc(void){
Ch_plant_m1_1_1_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<5000.0;i++)
{
if (true&&Ch_plant_m1_1_1_w && !Ch_plant_m1_1_1_r)
{plant_v1_1=plant_v1_1+((control_1_0/plant_m1_1)-(1.622))*0.002;
plant_m1_1=plant_m1_1+(-(control_1_0/(2842)))*0.002;
plant_r1_1=plant_r1_1+(plant_v1_1)*0.002;
wait(0.002,SC_SEC);wait(0,SC_SEC,Ch_plant_m1_1_1_w.posedge_event());
}
else 
break;
}
if (!true&&Ch_plant_m1_1_1_w && !Ch_plant_m1_1_1_r)
{Ch_plant_m1_1_1_w=0;
wait(SC_ZERO_TIME);
}
if (Ch_plant_m1_1_1_w && Ch_plant_m1_1_1_r){
int count=0,a[1],j=-1;
if (Ch_plant_m1_1_1_w&&Ch_plant_m1_1_1_r) {a[0]=1;count++;}
int k=rand()%count;
while(k>=0){j++;if(a[j])k--;}
switch(j){
case 0:
Ch_plant_m1_1_1.write(plant_m1_1);
wait(SC_ZERO_TIME);
Ch_plant_m1_1_1_w_done.notify();
wait(Ch_plant_m1_1_1_r_done);
Ch_plant_m1_1_1_w=0;
wait(SC_ZERO_TIME);
Ch_plant_m1_1_1_w=0;
wait(SC_ZERO_TIME);
interrupt_4_proc();
break;
}
}
if (true&& Ch_plant_m1_1_1_w && !Ch_plant_m1_1_1_r){
plant_v1_1=0.0;
plant_m1_1=0.0;
plant_r1_1=0.0;
wait(SC_ZERO_TIME);
return;
}
}
void PC1_3(void){
if (((control_1_0<=(3000))))
{
domain_4_proc();
}
}
void PC1_init(void){
PC1_1();
commI1();
}
void PC1_rep(void){
PC1_2();
PC1_3();
}
void PC1(void){
PC1_init();
while (true)
{
PC1_rep();
}
}
void PD1_1(void){
control_1=(2027.5);
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
Ch_plant_m1_1_1_r=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_m1_1_1_w) wait(Ch_plant_m1_1_1_w.posedge_event());
wait(Ch_plant_m1_1_1_w_done);
plant_m1_1_1=Ch_plant_m1_1_1.read();
wait(SC_ZERO_TIME);
Ch_plant_m1_1_1_r_done.notify();
Ch_plant_m1_1_1_r=0;
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_r=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_v1_1_1_w) wait(Ch_plant_v1_1_1_w.posedge_event());
wait(Ch_plant_v1_1_1_w_done);
plant_v1_1_1=Ch_plant_v1_1_1.read();
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_r_done.notify();
Ch_plant_v1_1_1_r=0;
wait(SC_ZERO_TIME);
}
void PD1_3(void){
control_1=(plant_m1_1_1*((1.622)-(0.01)*(control_1/plant_m1_1_1-(1.622))-(0.6)*(plant_v1_1_1+(2))));
wait(SC_ZERO_TIME);
}
void PD1_4(void){
wait(0.128,SC_SEC);
}
void PD1_5(void){
Ch_plant_m1_1_1_r=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_m1_1_1_w) wait(Ch_plant_m1_1_1_w.posedge_event());
wait(Ch_plant_m1_1_1_w_done);
plant_m1_1_1=Ch_plant_m1_1_1.read();
wait(SC_ZERO_TIME);
Ch_plant_m1_1_1_r_done.notify();
Ch_plant_m1_1_1_r=0;
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_r=1;
wait(SC_ZERO_TIME);
if (!Ch_plant_v1_1_1_w) wait(Ch_plant_v1_1_1_w.posedge_event());
wait(Ch_plant_v1_1_1_w_done);
plant_v1_1_1=Ch_plant_v1_1_1.read();
wait(SC_ZERO_TIME);
Ch_plant_v1_1_1_r_done.notify();
Ch_plant_v1_1_1_r=0;
wait(SC_ZERO_TIME);
}
void PD1_6(void){
control_1=(plant_m1_1_1*((1.622)-(0.01)*(control_1/plant_m1_1_1-(1.622))-(0.6)*(plant_v1_1_1+(2))));
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
P myinstance("myinstance");
myinstance.plant_v1_1(s[0]);
myinstance.plant_m1_1(s[1]);
myinstance.control_1(s[2]);
myinstance.plant_r1_1(s[3]);
myinstance.plant_v1_1_1(s[4]);
myinstance.plant_m1_1_1(s[5]);
myinstance.control_1_0(s[6]);
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
cout<<"plant_v1_1: ["<<mytest0.min<<", "<<mytest0.max<<"]"<<endl;
cout<<"plant_m1_1: ["<<mytest1.min<<", "<<mytest1.max<<"]"<<endl;
cout<<"control_1: ["<<mytest2.min<<", "<<mytest2.max<<"]"<<endl;
cout<<"plant_r1_1: ["<<mytest3.min<<", "<<mytest3.max<<"]"<<endl;
cout<<"plant_v1_1_1: ["<<mytest4.min<<", "<<mytest4.max<<"]"<<endl;
cout<<"plant_m1_1_1: ["<<mytest5.min<<", "<<mytest5.max<<"]"<<endl;
cout<<"control_1_0: ["<<mytest6.min<<", "<<mytest6.max<<"]"<<endl;
return 0;
}
