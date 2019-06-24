#include"systemc.h"


SC_MODULE(PWriter2_2){
sc_out<double> E1;
sc_out<double> done1;
sc_out<double> SE;
sc_out<double> num;
sc_out<double> EL;
sc_out<double> NL;
sc_out<double> sfTemp1;
sc_out<double> ResponseDelay;
sc_out<double> re_changes;
sc_out<double> cansend;
sc_out<double> ACKNACK;
sc_out<double> flag;
sc_out<double> event;
sc_out<double> event1;
sc_out<double> actrepairing;
sc_out<double> actwaiting;
sc_out<double> actmust_repair;
sc_out<double> cansend1;
sc_out<double> ACKNACK1;
sc_out<double> flag1;
sc_out<double> re_changes1;
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
sc_signal<double> Ch_Writer2_2_1;
sc_signal<bool> Ch_Writer2_2_1_r,Ch_Writer2_2_1_w;
sc_event Ch_Writer2_2_1_r_done,Ch_Writer2_2_1_w_done;

SC_CTOR(PWriter2_2){
SC_THREAD(PWriter2_26);
SC_THREAD(PWriter2_27);
}
void PWriter2_21(void){
if ((num==0))
{
Statement0();
}
}
void PWriter2_22(void){
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
VO1.write(ACKNACK);
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
VO1.write(re_changes);
wait(SC_ZERO_TIME);
VO1_w_done.notify();
wait(VO1_r_done);
VO1_w=0;
wait(SC_ZERO_TIME);
}
void PWriter2_23(void){
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
ACKNACK=VI1.read();
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
re_changes=VI1.read();
wait(SC_ZERO_TIME);
VI1_r_done.notify();
VI1_r=0;
wait(SC_ZERO_TIME);
}
void PWriter2_24(void){
if ((num==1))
{
Statement1();
}
}
void PWriter2_25(void){
if ((num==2))
{
Statement2();
}
}
void PWriter2_26(void){
((num=0;
wait(SC_ZERO_TIME);
SE=(String'''');
wait(SC_ZERO_TIME);
(actrepairing=0);
wait(SC_ZERO_TIME);
(actwaiting=0);
wait(SC_ZERO_TIME);
(actmust_repair=0));
wait(SC_ZERO_TIME);
Skip)();
(PWriter2_21();
PWriter2_22();
PWriter2_23)*();
}
void PWriter2_27(void){
(actrepairing=0);
wait(SC_ZERO_TIME);
(actwaiting=0);
wait(SC_ZERO_TIME);
(actmust_repair=0);
wait(SC_ZERO_TIME);
(re_changes=0;
wait(SC_ZERO_TIME);
Skip();
actwaiting=1;
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
cansend1=VO1.read();
wait(SC_ZERO_TIME);
VO1_r_done.notify();
VO1_r=0;
wait(SC_ZERO_TIME);
VO1_r=1;
wait(SC_ZERO_TIME);
if (!VO1_w) wait(VO1_w.posedge_event());
wait(VO1_w_done);
ACKNACK1=VO1.read();
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
re_changes1=VO1.read();
wait(SC_ZERO_TIME);
VO1_r_done.notify();
VO1_r=0;
wait(SC_ZERO_TIME);
if ((actrepairing==1))
{
Statement6();
}
if ((actwaiting==1))
{
Statement10();
}
if ((actmust_repair==1))
{
Statement14();
}
BO_1_w=1;
wait(SC_ZERO_TIME);
if (!BO_1_r) wait(BO_1_r.posedge_event());
BO_1.write((String''''));
wait(SC_ZERO_TIME);
BO_1_w_done.notify();
wait(BO_1_r_done);
BO_1_w=0;
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
VI1.write(ACKNACK1);
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
VI1.write(re_changes1)*);
wait(SC_ZERO_TIME);
VI1_w_done.notify();
wait(VI1_r_done);
VI1_w=0;
wait(SC_ZERO_TIME);
}
void Statement0(void){
<(WTrue)&&(WTrue)>:(l==0.01);
wait(SC_ZERO_TIME);
(num=1;
wait(SC_ZERO_TIME);
empty(EL)();
(addLELSE)();
empty(NL)();
(addLNL1))();
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
PWriter2_22();
((BR_1_r=1;
wait(SC_ZERO_TIME);
if (!((BR_1_w) wait(((BR_1_w.posedge_event());
wait(((BR_1_w_done);
SE=((BR_1.read();
wait(SC_ZERO_TIME);
((BR_1_r_done.notify();
((BR_1_r=0;
wait(SC_ZERO_TIME);
(addLELSE)();
(addLNL1)();
num=1)[[BO_1??vBO1;
wait(SC_ZERO_TIME);
PWriter2_23)();
num=(num+1);
wait(SC_ZERO_TIME);
delL(NL)();
(addLNLnum)();
}
void Statement2(void){
num=0;
wait(SC_ZERO_TIME);
SE=0;
wait(SC_ZERO_TIME);
}
void Statement3(void){
actrepairing=0;
wait(SC_ZERO_TIME);
actwaiting=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement4(void){
re_changes=(re_changes-1);
wait(SC_ZERO_TIME);
actrepairing=0;
wait(SC_ZERO_TIME);
actrepairing=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement5(void){
flag=0;
wait(SC_ZERO_TIME);
}
void Statement6(void){
if (((done1==0)&&re_changes==0))
{
Statement3();
}
if (((done1==0)&&cansend==1))
{
Statement4();
}
if ((done1==0))
{
Statement5();
}
}
void Statement7(void){
actwaiting=0;
wait(SC_ZERO_TIME);
actmust_repair=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement8(void){
re_changes=(re_changes+1);
wait(SC_ZERO_TIME);
actwaiting=0;
wait(SC_ZERO_TIME);
actwaiting=1;
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
if (((done1==0)&&re_changes>0))
{
Statement7();
}
if (((done1==0)&&ACKNACK==1))
{
Statement8();
}
if ((done1==0))
{
Statement9();
}
}
void Statement11(void){
actmust_repair=0;
wait(SC_ZERO_TIME);
actrepairing=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement12(void){
re_changes=(re_changes+1);
wait(SC_ZERO_TIME);
actmust_repair=0;
wait(SC_ZERO_TIME);
actmust_repair=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement13(void){
flag=1;
wait(SC_ZERO_TIME);
Skip();
}
void Statement14(void){
if (((done1==0)&&E1==(String''after(ResponseDelay,sec)'')))
{
Statement11();
}
if (((done1==0)&&ACKNACK==1))
{
Statement12();
}
if ((done1==0))
{
Statement13();
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
sc_signal<double> s[21];
PWriter2_2 myinstance("myinstance");
myinstance.E1(s[0]);
myinstance.done1(s[1]);
myinstance.SE(s[2]);
myinstance.num(s[3]);
myinstance.EL(s[4]);
myinstance.NL(s[5]);
myinstance.sfTemp1(s[6]);
myinstance.ResponseDelay(s[7]);
myinstance.re_changes(s[8]);
myinstance.cansend(s[9]);
myinstance.ACKNACK(s[10]);
myinstance.flag(s[11]);
myinstance.event(s[12]);
myinstance.event1(s[13]);
myinstance.actrepairing(s[14]);
myinstance.actwaiting(s[15]);
myinstance.actmust_repair(s[16]);
myinstance.cansend1(s[17]);
myinstance.ACKNACK1(s[18]);
myinstance.flag1(s[19]);
myinstance.re_changes1(s[20]);
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
cout<<"ResponseDelay: ["<<mytest7.values[j]<<"]"<<endl;
cout<<"re_changes: ["<<mytest8.values[j]<<"]"<<endl;
cout<<"cansend: ["<<mytest9.values[j]<<"]"<<endl;
cout<<"ACKNACK: ["<<mytest10.values[j]<<"]"<<endl;
cout<<"flag: ["<<mytest11.values[j]<<"]"<<endl;
cout<<"event: ["<<mytest12.values[j]<<"]"<<endl;
cout<<"event1: ["<<mytest13.values[j]<<"]"<<endl;
cout<<"actrepairing: ["<<mytest14.values[j]<<"]"<<endl;
cout<<"actwaiting: ["<<mytest15.values[j]<<"]"<<endl;
cout<<"actmust_repair: ["<<mytest16.values[j]<<"]"<<endl;
cout<<"cansend1: ["<<mytest17.values[j]<<"]"<<endl;
cout<<"ACKNACK1: ["<<mytest18.values[j]<<"]"<<endl;
cout<<"flag1: ["<<mytest19.values[j]<<"]"<<endl;
cout<<"re_changes1: ["<<mytest20.values[j]<<"]"<<endl;
}
return 0;
}
