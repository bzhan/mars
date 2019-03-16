sdpvar t v w1
sdpvar myeps0
sdpvar myeps1
sdpvar myeps2
sdpvar myeps3

lambda1 = .5;
lambda2 = 1;

tol0 = 1e-3;
tol1 = 1e-4;
tol2 = 1e-4;
tol3 = 1e-4;

[inv, c0] = polynomial([t v w1], 6);
[s1, c1] = polynomial([t v w1], 4);
[s2, c2] = polynomial([t v w1], 4);
[s3, c3] = polynomial([t v w1], 4);
[s4, c4] = polynomial([t v w1], 4);

flow=[1.; -1.622 + w1; 0.0003924646781789639*w1^2];
dinv=[jacobian(inv,t),jacobian(inv,v),jacobian(inv,w1)];
lie=dinv*flow;

p_init3=replace(inv,t,0.);
p_init2=replace(p_init3,v,-2.);
p_init1=replace(p_init2,w1,1.622);
f0=p_init1 <= -myeps0;

f1=sos(-lie-lambda1*inv - s1*(0.128 - t)*(0. + t) - myeps1);

f2=sos(inv - s2*(0. + t)*(0.128 - t) - s3*(1.95 + v)*(2.05 + v) - myeps2);

rst_inv1 = replace(inv, t, 0.);
rst_inv2 = replace(rst_inv1, w1, 1.622 - 0.6*(2. + v) + 0.01*(1.622 - 1.*w1));

f3=sos(lambda2*inv - rst_inv2 - s4*(-0.128 + t) - myeps3);

FeasibilityConstraints=[f0,f1,f2,f3,sos(s1),sos(s2),sos(s3),myeps0>=tol0,myeps1>=tol1,myeps2>=tol2,myeps3>=tol3];

options=sdpsettings('verbose',0,'solver','mosek');

solvesos(FeasibilityConstraints,[ ],options,[c0;c1;c2;c3;c4;myeps0;myeps1;myeps2;myeps3])

mono_inv=monolist([t v w1], 6);
pinv=double(c0')*mono_inv;
sdisplay(clean(pinv,1e-3))
