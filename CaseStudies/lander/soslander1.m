format long
sdpvar t V w
sdpvar myeps0
sdpvar myeps1
sdpvar myeps2
sdpvar myeps3

lambda1 = 0.5;
lambda2 = 1;

tol0 = 1e-2;
tol1 = 1e-4;
tol2 = 1e-4;
tol3 = 1e-4;
tol4 = 1e-4;

[r1, b1] = polynomial([V w], 4);
[r2, b2] = polynomial([V w], 3);
inv = r1 + r2 * t;
[s1, c1] = polynomial([V w], 2);
[s2, c2] = polynomial([V w], 2);
[s3, c3] = polynomial([V w], 2);

flow=[1.; -3.732 + w; 0.0004*w^2];
dinv=[jacobian(inv,t),jacobian(inv,V),jacobian(inv,w)];
lie=dinv*flow;

p_init3=replace(inv,t,0.);
p_init2=replace(p_init3,V,-1.5);
p_init1=replace(p_init2,w,2835/759.5);
f0=p_init1 <= -myeps0;

f1=sos(-lie-lambda1*inv - s1*(0.128 - t)*(0. + t) - myeps1);

f2=sos(inv - s2*(0. + t)*(0.128 - t) - s3*(1.45 + V)*(1.55 + V) - myeps2);

rst_inv1 = replace(inv, t, 0.);
rst_inv2 = replace(rst_inv1, w, 3.732 - 0.6*(1.5 + V) - 0.01*(w-3.732));
rst_inv3 = replace(inv, t, 0.128);

f3=sos(lambda2*rst_inv3 - rst_inv2 - myeps3);

FeasibilityConstraints=[f0,f1,f2,f3,sos(s1),sos(s2),sos(s3),myeps0>=tol0,myeps1>=tol1,myeps2>=tol2,myeps3>=tol3];

options=sdpsettings('verbose',0,'solver','mosek');

solvesos(FeasibilityConstraints,[ ],options,[b1;b2;c1;c2;c3;myeps0;myeps1;myeps2;myeps3])

mono_r1=monolist([V w], 4);
mono_r2=monolist([V w], 3);
pinv=value(b1')*mono_r1 + (value(b2')*mono_r2)*t;
sdisplay(clean(pinv,1e-3));
g0 = replace(pinv,t,0.0);
g1 = replace(g0,V,-1.5);
g2 = replace(g1,w,2835/759.5);
%sdisplay(g2)
%pdinv=[jacobian(pinv,t),jacobian(pinv,V),jacobian(pinv,w)];
%plie=pdinv*flow;
%sdisplay(plie);
mono_s=monolist([V w], 2);
ps1=value(c1')*mono_s;
sdisplay(clean(ps1,1e-3));
%value(myeps1)
ps2=value(c2')*mono_s;
ps3=value(c3')*mono_s;
%sdisplay(-plie-lambda1*pinv - ps1*(0.128 - t)*(0. + t));
%sdisplay(pinv - ps2*(0. + t)*(0.128 - t) - ps3*(1.45 + V)*(1.55 + V));
