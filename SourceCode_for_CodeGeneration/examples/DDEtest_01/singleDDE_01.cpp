#include"systemc.h"

const double delay=1.3;

SC_MODULE(singleDDE_01){
sc_out<double> y;

SC_CTOR(singleDDE_01){
SC_THREAD(DDE_01);
}
void DDE_01(void){
double y_values[16]={0.581250,0.675703,0.785505,0.913149,1.061536,1.206005,1.333113,1.426046,1.466298,1.436973,1.340766,1.195612,1.030062,0.873959,0.749843,0.666798};
for (int i=0;i<16.0;i++)
{
if (true&&true)
{
wait(0.325,SC_SEC);
y=y_values[i];
wait(SC_ZERO_TIME);
}
else 
break;
}
if (true&&true)
{
return;
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
sc_signal<double> s[1];
singleDDE_01 myinstance("myinstance");
myinstance.y(s[0]);
test mytest0("mytest0");
mytest0.s_in(s[0]);
sc_start(+5.0,SC_SEC);
cout<<"y: ["<<mytest0.min<<", "<<mytest0.max<<"]"<<endl;
return 0;
}
