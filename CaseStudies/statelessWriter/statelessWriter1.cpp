#include"systemc.h"


SC_MODULE(Statement9){
sc_out<double> E1;
sc_out<double> done1;
sc_out<double> SE;
sc_out<double> num;
sc_out<double> EL;
sc_out<double> NL;
sc_out<double> sfTemp1;
sc_out<double> unsent;
sc_out<double> a;
sc_out<double> cansend;
sc_out<double> flag;
sc_out<double> actpushing;
sc_out<double> actidle;
sc_out<double> a1;
sc_out<double> cansend1;
sc_out<double> flag1;
sc_out<double> unsent1;
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
sc_signal<double> Ch_Writer1_1;
sc_signal<bool> Ch_Writer1_1_r,Ch_Writer1_1_w;
sc_event Ch_Writer1_1_r_done,Ch_Writer1_1_w_done;

SC_CTOR(Statement9){
SC_THREAD(if((done1==0)&&unsent>0)thenStatement7elseSkipif(done1==0)thenStatement8elseSkip);
}
void PWriter1(void){
PWriter16||PWriter17();
}
void PWriter11(void){
if ((num==0))
{
Statement0();
}
}
void PWriter12(void){
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
VO1.write(unsent);
wait(SC_ZERO_TIME);
VO1_w_done.notify();
wait(VO1_r_done);
VO1_w=0;
wait(SC_ZERO_TIME);
}
void PWriter13(void){
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
unsent=VI1.read();
wait(SC_ZERO_TIME);
VI1_r_done.notify();
VI1_r=0;
wait(SC_ZERO_TIME);
}
void PWriter14(void){
if ((num==1))
{
Statement1();
}
}
void PWriter15(void){
if ((num==2))
{
Statement2();
}
}
void PWriter16(void){
((num=0;
wait(SC_ZERO_TIME);
SE=0;
wait(SC_ZERO_TIME);
(actpushing=0);
wait(SC_ZERO_TIME);
(actidle=0));
wait(SC_ZERO_TIME);
Skip)();
(PWriter11();
PWriter12();
PWriter13)*();
}
void PWriter17(void){
(actpushing=0);
wait(SC_ZERO_TIME);
(actidle=0);
wait(SC_ZERO_TIME);
(unsent=(a);
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
unsent1=VO1.read();
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
Statement9();
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
VI1.write(unsent1)*);
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
PWriter12();
(BO_1_r=1;
wait(SC_ZERO_TIME);
if (!(BO_1_w) wait((BO_1_w.posedge_event());
wait((BO_1_w_done);
vBO1=(BO_1.read();
wait(SC_ZERO_TIME);
(BO_1_r_done.notify();
(BO_1_r=0;
wait(SC_ZERO_TIME);
PWriter13)();
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
actidle=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement4(void){
unsent=(unsent-1);
wait(SC_ZERO_TIME);
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
if (((done1==0)&&unsent<=0))
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
actidle=0;
wait(SC_ZERO_TIME);
actpushing=1;
wait(SC_ZERO_TIME);
done1=1;
wait(SC_ZERO_TIME);
}
void Statement8(void){
flag=1;
wait(SC_ZERO_TIME);
Skip();
}
void Statement9(void){
if (((done1==0)&&unsent>0))
{
Statement7();
}
if ((done1==0))
{
Statement8();
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
sc_signal<double> s[17];
Statement9 myinstance("myinstance");
myinstance.E1(s[0]);
myinstance.done1(s[1]);
myinstance.SE(s[2]);
myinstance.num(s[3]);
myinstance.EL(s[4]);
myinstance.NL(s[5]);
myinstance.sfTemp1(s[6]);
myinstance.unsent(s[7]);
myinstance.a(s[8]);
myinstance.cansend(s[9]);
myinstance.flag(s[10]);
myinstance.actpushing(s[11]);
myinstance.actidle(s[12]);
myinstance.a1(s[13]);
myinstance.cansend1(s[14]);
myinstance.flag1(s[15]);
myinstance.unsent1(s[16]);
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
cout<<"unsent: ["<<mytest7.values[j]<<"]"<<endl;
cout<<"a: ["<<mytest8.values[j]<<"]"<<endl;
cout<<"cansend: ["<<mytest9.values[j]<<"]"<<endl;
cout<<"flag: ["<<mytest10.values[j]<<"]"<<endl;
cout<<"actpushing: ["<<mytest11.values[j]<<"]"<<endl;
cout<<"actidle: ["<<mytest12.values[j]<<"]"<<endl;
cout<<"a1: ["<<mytest13.values[j]<<"]"<<endl;
cout<<"cansend1: ["<<mytest14.values[j]<<"]"<<endl;
cout<<"flag1: ["<<mytest15.values[j]<<"]"<<endl;
cout<<"unsent1: ["<<mytest16.values[j]<<"]"<<endl;
}
return 0;
}
