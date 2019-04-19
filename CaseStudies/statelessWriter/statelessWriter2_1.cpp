#include"systemc.h"


SC_MODULE(Statement10){
sc_out<double> E1;
sc_out<double> done1;
sc_out<double> SE;
sc_out<double> num;
sc_out<double> EL;
sc_out<double> NL;
sc_out<double> sfTemp1;
sc_out<double> heartbeatPeriod;
sc_out<double> i;
sc_out<double> a;
sc_out<double> cansend;
sc_out<double> flag;
sc_out<double> heartbeat;
sc_out<double> event;
sc_out<double> event1;
sc_out<double> actpushing;
sc_out<double> actidle;
sc_out<double> a1;
sc_out<double> cansend1;
sc_out<double> flag1;
sc_out<double> heartbeat1;
sc_out<double> i1;
sc_signal<double> BC_1;
sc_signal<bool> BC_1_r,BC_1_w;
sc_event BC_1_r_done,BC_1_w_done;
sc_signal<double> BR_1;
sc_signal<bool> BR_1_r,BR_1_w;
sc_event BR_1_r_done,BR_1_w_done;
sc_signal<double> BO_1;
sc_signal<bool> BO_1_r,BO_1_w;
sc_event BO_1_r_done,BO_1_w_done;
sc_signal<double> VO1;
sc_signal<bool> VO1_r,VO1_w;
sc_event VO1_r_done,VO1_w_done;
sc_signal<double> VI1;
sc_signal<bool> VI1_r,VI1_w;
sc_event VI1_r_done,VI1_w_done;
sc_signal<double> vBO1;
sc_signal<bool> vBO1_r,vBO1_w;
sc_event vBO1_r_done,vBO1_w_done;
sc_signal<double> Ch_Writer2_1_1;
sc_signal<bool> Ch_Writer2_1_1_r,Ch_Writer2_1_1_w;
sc_event Ch_Writer2_1_1_r_done,Ch_Writer2_1_1_w_done;

SC_CTOR(Statement10){
SC_THREAD(if((done1==0)&&i>0)thenStatement7elseSkipif((done1==0)&&E1==0)thenStatement8elseSkipif(done1==0)thenStatement9elseSkip);
}
void PWriter2_1(void){
PWriter2_16||PWriter2_17();
}
void PWriter2_11(void){
if ((num==0))
{
Statement0();
}
}
void PWriter2_12(void){
VO1_w=1;
wait(SC_ZERO_TIME);
if (!VO1_r) wait(VO1_r.posedge_event());
VO1.write(a);
wait(SC_ZERO_TIME);
VO1_w_done.notify();
wait(VO1_r_done);
VO1_w=0;
wait(SC_ZERO_TIME);
VO1_w=1;
wait(SC_ZERO_TIME);
if (!VO1_r) wait(VO1_r.posedge_event());
VO1.write(cansend);
wait(SC_ZERO_TIME);
VO1_w_done.notify();
wait(VO1_r_done);
VO1_w=0;
wait(SC_ZERO_TIME);
VO1_w=1;
wait(SC_ZERO_TIME);
if (!VO1_r) wait(VO1_r.posedge_event());
VO1.write(flag);
wait(SC_ZERO_TIME);
VO1_w_done.notify();
wait(VO1_r_done);
VO1_w=0;
wait(SC_ZERO_TIME);
VO1_w=1;
wait(SC_ZERO_TIME);
if (!VO1_r) wait(VO1_r.posedge_event());
VO1.write(heartbeat);
wait(SC_ZERO_TIME);
VO1_w_done.notify();
wait(VO1_r_done);
VO1_w=0;
wait(SC_ZERO_TIME);
VO1_w=1;
wait(SC_ZERO_TIME);
if (!VO1_r) wait(VO1_r.posedge_event());
VO1.write(i);
wait(SC_ZERO_TIME);
VO1_w_done.notify();
wait(VO1_r_done);
VO1_w=0;
wait(SC_ZERO_TIME);
}
void PWriter2_13(void){
VI1_r=1;
wait(SC_ZERO_TIME);
if (!VI1_w) wait(VI1_w.posedge_event());
wait(VI1_w_done);
a=VI1.read();
wait(SC_ZERO_TIME);
VI1_r_done.notify();
VI1_r=0;
wait(SC_ZERO_TIME);
VI1_r=1;
wait(SC_ZERO_TIME);
if (!VI1_w) wait(VI1_w.posedge_event());
wait(VI1_w_done);
cansend=VI1.read();
wait(SC_ZERO_TIME);
VI1_r_done.notify();
VI1_r=0;
wait(SC_ZERO_TIME);
VI1_r=1;
wait(SC_ZERO_TIME);
if (!VI1_w) wait(VI1_w.posedge_event());
wait(VI1_w_done);
flag=VI1.read();
wait(SC_ZERO_TIME);
VI1_r_done.notify();
VI1_r=0;
wait(SC_ZERO_TIME);
VI1_r=1;
wait(SC_ZERO_TIME);
if (!VI1_w) wait(VI1_w.posedge_event());
wait(VI1_w_done);
heartbeat=VI1.read();
wait(SC_ZERO_TIME);
VI1_r_done.notify();
VI1_r=0;
wait(SC_ZERO_TIME);
VI1_r=1;
wait(SC_ZERO_TIME);
if (!VI1_w) wait(VI1_w.posedge_event());
wait(VI1_w_done);
i=VI1.read();
wait(SC_ZERO_TIME);
VI1_r_done.notify();
VI1_r=0;
wait(SC_ZERO_TIME);
}
void PWriter2_14(void){
if ((num==1))
{
Statement1();
}
}
void PWriter2_15(void){
if ((num==2))
{
Statement2();
}
}
void PWriter2_16(void){
((num=0;
wait(SC_ZERO_TIME);
SE=0;
wait(SC_ZERO_TIME);
(actpushing=0);
wait(SC_ZERO_TIME);
(actidle=0));
wait(SC_ZERO_TIME);
Skip)();
(PWriter2_11();
PWriter2_12();
PWriter2_13)*();
}
void PWriter2_17(void){
(actpushing=0);
wait(SC_ZERO_TIME);
(actidle=0);
wait(SC_ZERO_TIME);
(i=(a);
wait(SC_ZERO_TIME);
Skip();
heartbeat=0;
wait(SC_ZERO_TIME);
heartbeat=0;
wait(SC_ZERO_TIME);
Skip();
actidle=1;
wait(SC_ZERO_TIME);
Skip)();
(BC_1_r=1;
wait(SC_ZERO_TIME);
if (!(BC_1_w) wait((BC_1_w.posedge_event());
wait((BC_1_w_done);
E1=(BC_1.read();
wait(SC_ZERO_TIME);
(BC_1_r_done.notify();
(BC_1_r=0;
wait(SC_ZERO_TIME);
VO1_r=1;
wait(SC_ZERO_TIME);
if (!VO1_w) wait(VO1_w.posedge_event());
wait(VO1_w_done);
a1=VO1.read();
wait(SC_ZERO_TIME);
VO1_r_done.notify();
VO1_r=0;
wait(SC_ZERO_TIME);
VO1_r=1;
wait(SC_ZERO_TIME);
if (!VO1_w) wait(VO1_w.posedge_event());
wait(VO1_w_done);
cansend1=VO1.read();
wait(SC_ZERO_TIME);
VO1_r_done.notify();
VO1_r=0;
wait(SC_ZERO_TIME);
VO1_r=1;
wait(SC_ZERO_TIME);
if (!VO1_w) wait(VO1_w.posedge_event());
wait(VO1_w_done);
flag1=VO1.read();
wait(SC_ZERO_TIME);
VO1_r_done.notify();
VO1_r=0;
wait(SC_ZERO_TIME);
VO1_r=1;
wait(SC_ZERO_TIME);
if (!VO1_w) wait(VO1_w.posedge_event());
wait(VO1_w_done);
heartbeat1=VO1.read();
wait(SC_ZERO_TIME);
VO1_r_done.notify();
VO1_r=0;
wait(SC_ZERO_TIME);
VO1_r=1;
wait(SC_ZERO_TIME);
if (!VO1_w) wait(VO1_w.posedge_event());
wait(VO1_w_done);
i1=VO1.read();
wait(SC_ZERO_TIME);
VO1_r_done.notify();
VO1_r=0;
wait(SC_ZERO_TIME);
if ((actpushing==1))
{
Statement6();
}
if ((actidle==1))
{
Statement10();
}
BO_1_w=1;
wait(SC_ZERO_TIME);
if (!BO_1_r) wait(BO_1_r.posedge_event());
BO_1.write(0);
wait(SC_ZERO_TIME);
BO_1_w_done.notify();
wait(BO_1_r_done);
BO_1_w=0;
wait(SC_ZERO_TIME);
VI1_w=1;
wait(SC_ZERO_TIME);
if (!VI1_r) wait(VI1_r.posedge_event());
VI1.write(a1);
wait(SC_ZERO_TIME);
VI1_w_done.notify();
wait(VI1_r_done);
VI1_w=0;
wait(SC_ZERO_TIME);
VI1_w=1;
wait(SC_ZERO_TIME);
if (!VI1_r) wait(VI1_r.posedge_event());
VI1.write(cansend1);
wait(SC_ZERO_TIME);
VI1_w_done.notify();
wait(VI1_r_done);
VI1_w=0;
wait(SC_ZERO_TIME);
VI1_w=1;
wait(SC_ZERO_TIME);
if (!VI1_r) wait(VI1_r.posedge_event());
VI1.write(flag1);
wait(SC_ZERO_TIME);
VI1_w_done.notify();
wait(VI1_r_done);
VI1_w=0;
wait(SC_ZERO_TIME);
VI1_w=1;
wait(SC_ZERO_TIME);
if (!VI1_r) wait(VI1_r.posedge_event());
VI1.write(heartbeat1);
wait(SC_ZERO_TIME);
VI1_w_done.notify();
wait(VI1_r_done);
VI1_w=0;
wait(SC_ZERO_TIME);
VI1_w=1;
wait(SC_ZERO_TIME);
if (!VI1_r) wait(VI1_r.posedge_event());
VI1.write(i1)*);
wait(SC_ZERO_TIME);
VI1_w_done.notify();
wait(VI1_r_done);
VI1_w=0;
wait(SC_ZERO_TIME);
}
void Statement0(void){
(num=1);
wait(SC_ZERO_TIME);
}
void Statement1(void){
BC_1_w=1;
wait(SC_ZERO_TIME);
if (!BC_1_r) wait(BC_1_r.posedge_event());
BC_1.write(SE);
wait(SC_ZERO_TIME);
BC_1_w_done.notify();
wait(BC_1_r_done);
BC_1_w=0;
wait(SC_ZERO_TIME);
PWriter2_12();
(BO_1_r=1;
wait(SC_ZERO_TIME);
if (!(BO_1_w) wait((BO_1_w.posedge_event());
wait((BO_1_w_done);
vBO1=(BO_1.read();
wait(SC_ZERO_TIME);
(BO_1_r_done.notify();
(BO_1_r=0;
wait(SC_ZERO_TIME);
PWriter2_13)();
num=(num+1);
wait(SC_ZERO_TIME);
}
void Statement2(void){
num=0;
wait(SC_ZERO_TIME);
SE=0;
wait(SC_ZERO_TIME);
}
void Statement3(void){
actpushing=0;
wait(SC_ZERO_TIME);
heartbeat=0;
wait(SC_ZERO_TIME);
heartbeat=0;
wait(SC_ZERO_TIME);
Skip();
actidle=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement4(void){
actpushing=0;
wait(SC_ZERO_TIME);
actpushing=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement5(void){
flag=0;
wait(SC_ZERO_TIME);
}
void Statement6(void){
if (((done1==0)&&i<=0))
{
Statement3();
}
if (((done1==0)))
{
Statement4();
}
if ((done1==0))
{
Statement5();
}
}
void Statement7(void){
actidle=0;
wait(SC_ZERO_TIME);
actpushing=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement8(void){
heartbeat=1;
wait(SC_ZERO_TIME);
actidle=0;
wait(SC_ZERO_TIME);
heartbeat=0;
wait(SC_ZERO_TIME);
Skip();
actidle=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement9(void){
flag=1;
wait(SC_ZERO_TIME);
Skip();
}
void Statement10(void){
if (((done1==0)&&i>0))
{
Statement7();
}
if (((done1==0)&&E1==0))
{
Statement8();
}
if ((done1==0))
{
Statement9();
}
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
sc_signal<double> s[22];
Statement10 myinstance("myinstance");
myinstance.E1(s[0]);
myinstance.done1(s[1]);
myinstance.SE(s[2]);
myinstance.num(s[3]);
myinstance.EL(s[4]);
myinstance.NL(s[5]);
myinstance.sfTemp1(s[6]);
myinstance.heartbeatPeriod(s[7]);
myinstance.i(s[8]);
myinstance.a(s[9]);
myinstance.cansend(s[10]);
myinstance.flag(s[11]);
myinstance.heartbeat(s[12]);
myinstance.event(s[13]);
myinstance.event1(s[14]);
myinstance.actpushing(s[15]);
myinstance.actidle(s[16]);
myinstance.a1(s[17]);
myinstance.cansend1(s[18]);
myinstance.flag1(s[19]);
myinstance.heartbeat1(s[20]);
myinstance.i1(s[21]);
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
test mytest9("mytest9");
mytest9.s_in(s[9]);
test mytest10("mytest10");
mytest10.s_in(s[10]);
test mytest11("mytest11");
mytest11.s_in(s[11]);
test mytest12("mytest12");
mytest12.s_in(s[12]);
test mytest13("mytest13");
mytest13.s_in(s[13]);
test mytest14("mytest14");
mytest14.s_in(s[14]);
test mytest15("mytest15");
mytest15.s_in(s[15]);
test mytest16("mytest16");
mytest16.s_in(s[16]);
test mytest17("mytest17");
mytest17.s_in(s[17]);
test mytest18("mytest18");
mytest18.s_in(s[18]);
test mytest19("mytest19");
mytest19.s_in(s[19]);
test mytest20("mytest20");
mytest20.s_in(s[20]);
test mytest21("mytest21");
mytest21.s_in(s[21]);
sc_start(+10.0,SC_SEC);
for(int j=0;j<1100;j++)
{
cout<<"E1: ["<<mytest0.values[j]<<"]"<<endl;
cout<<"done1: ["<<mytest1.values[j]<<"]"<<endl;
cout<<"SE: ["<<mytest2.values[j]<<"]"<<endl;
cout<<"num: ["<<mytest3.values[j]<<"]"<<endl;
cout<<"EL: ["<<mytest4.values[j]<<"]"<<endl;
cout<<"NL: ["<<mytest5.values[j]<<"]"<<endl;
cout<<"sfTemp1: ["<<mytest6.values[j]<<"]"<<endl;
cout<<"heartbeatPeriod: ["<<mytest7.values[j]<<"]"<<endl;
cout<<"i: ["<<mytest8.values[j]<<"]"<<endl;
cout<<"a: ["<<mytest9.values[j]<<"]"<<endl;
cout<<"cansend: ["<<mytest10.values[j]<<"]"<<endl;
cout<<"flag: ["<<mytest11.values[j]<<"]"<<endl;
cout<<"heartbeat: ["<<mytest12.values[j]<<"]"<<endl;
cout<<"event: ["<<mytest13.values[j]<<"]"<<endl;
cout<<"event1: ["<<mytest14.values[j]<<"]"<<endl;
cout<<"actpushing: ["<<mytest15.values[j]<<"]"<<endl;
cout<<"actidle: ["<<mytest16.values[j]<<"]"<<endl;
cout<<"a1: ["<<mytest17.values[j]<<"]"<<endl;
cout<<"cansend1: ["<<mytest18.values[j]<<"]"<<endl;
cout<<"flag1: ["<<mytest19.values[j]<<"]"<<endl;
cout<<"heartbeat1: ["<<mytest20.values[j]<<"]"<<endl;
cout<<"i1: ["<<mytest21.values[j]<<"]"<<endl;
}
return 0;
}
