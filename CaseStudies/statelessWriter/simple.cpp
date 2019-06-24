#include"systemc.h"


SC_MODULE(P){
sc_out<double> x;
sc_out<double> y;
sc_out<double> z;
sc_signal<double> c;
sc_signal<bool> c_r,c_w;
sc_event c_r_done,c_w_done;

SC_CTOR(P){
SC_THREAD(P1);
SC_THREAD(P2);
}
void P1(void){
z=0;
wait(SC_ZERO_TIME);
if(z==0)then(c_w=1;
wait(SC_ZERO_TIME);
if (!if(z==0)then(c_r) wait(if(z==0)then(c_r.posedge_event());
if(z==0)then(c.write(x);
wait(SC_ZERO_TIME);
if(z==0)then(c_w_done.notify();
wait(if(z==0)then(c_r_done);
if(z==0)then(c_w=0;
wait(SC_ZERO_TIME);
z=z+1;
wait(SC_ZERO_TIME);
(z=z*2;
wait(SC_ZERO_TIME);
(z=z/3)))elseSkip;
wait(SC_ZERO_TIME);
}
void P2(void){
c_r=1;
wait(SC_ZERO_TIME);
if (!c_w) wait(c_w.posedge_event());
wait(c_w_done);
y=c.read();
wait(SC_ZERO_TIME);
c_r_done.notify();
c_r=0;
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
sc_signal<double> s[3];
P myinstance("myinstance");
myinstance.x(s[0]);
myinstance.y(s[1]);
myinstance.z(s[2]);
test mytest0("mytest0");
mytest0.s_in(s[0]);
test mytest1("mytest1");
mytest1.s_in(s[1]);
test mytest2("mytest2");
mytest2.s_in(s[2]);
sc_start(+10.0,SC_SEC);
for(int j=0;j<1100;j++)
{
cout<<"x: ["<<mytest0.values[j]<<"]"<<endl;
cout<<"y: ["<<mytest1.values[j]<<"]"<<endl;
cout<<"z: ["<<mytest2.values[j]<<"]"<<endl;
}
return 0;
}
