variables definition
wait(2,SC_SEC);
ch_w=1;
wait(SC_ZERO_TIME);
if (!ch_r) wait(ch_r.posedge_event());
ch.write(x);
wait(SC_ZERO_TIME);
ch_w_done.notify();
wait(ch_r_done);
ch_w=0;
wait(SC_ZERO_TIME);
x=1;
wait(SC_ZERO_TIME);
if (rand()%2)
{
x=1;
wait(SC_ZERO_TIME);
}
 else
{
y=1;
wait(SC_ZERO_TIME);
}
while (true)
{
x=1;
wait(SC_ZERO_TIME);
}
if (x==1)
{
x=x+1;
wait(SC_ZERO_TIME);
}
for (int i=0;i<0.0;i++)
{
if (return the epsilon neighborhood of B)
{
x=x+(x)*0.4;
wait(0.4,SC_SEC);
}
}
if (return the epsilon neighborhood of B)
{
x=0.0;
wait(SC_ZERO_TIME);
return;
}
wait(1,SC_SEC);
ch_r=1;
wait(SC_ZERO_TIME);
if (!ch_w) wait(ch_w.posedge_event());
wait(ch_w_done);
y=ch.read();
wait(SC_ZERO_TIME);
ch_r_done.notify();
ch_r=0;
wait(SC_ZERO_TIME);
y=1;
wait(SC_ZERO_TIME);
if (y==1)
{
y=0;
wait(SC_ZERO_TIME);
}
chh_w=1;
wait(SC_ZERO_TIME);

for (int i=0;i<0.0;i++)
{
if (return the epsilon neighborhood of B&&chh_w && !chh_r)
{y=y+(y+1)*0.4;
wait(0.4,SC_SEC);
}
}
if (!return the epsilon neighborhood of B&&chh_w && !chh_r)
{chh_w=0;
wait(SC_ZERO_TIME);
}
if (chh_w && chh_r){ int ones=0,a[1],choose;if (chh_w&&chh_r) {a[0]=1;ones++;}
k = rand()%ones;
for (int i=0;i<1;i++){if (a[i]==1) ones--;if (ones==0) break;}switch (i){case 0:chh.write(y);
wait(SC_ZERO_TIME);
chh_w_done.notify();
wait(chh_r_done);
chh_w=0;
wait(SC_ZERO_TIME);
chh_w=0;
wait(SC_ZERO_TIME);
y=1;
wait(SC_ZERO_TIME);
break;
}}
if (return the epsilon neighborhood of B&& chh_w && !chh_r){y=0.0;
wait(SC_ZERO_TIME);
return;
}