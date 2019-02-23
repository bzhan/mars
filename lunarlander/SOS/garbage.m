sdpvar parx;
sdpvar myeps0 myeps1 myeps2;

lambda1 = .5;
lambda2 = 1;

tol0 = 0;
tol1 = 0;
tol2 = 0;

[inv, c0] = polynomial([parx], 6);
[s1, c1] = polynomial([parx], 4);
[s2, c2] = polynomial([parx], 4);

f0 = sos(-inv - s1 * (parx-((1))) - myeps0);

f1 = sos(inv - s2 * (-(parx-((0)))) - myeps1);

flow0 = [((2))];
dinv0 = [jacobian(inv,parx)];
lie0 = dinv0 * flow0;
f2 = sos(-lie0 - lambda1 * inv - myeps2);

FeasibilityConstraints=[f0,f1,f2,sos(s1),sos(s2),myeps0>=tol0,myeps1>=tol1,myeps2>=tol2];

options=sdpsettings('verbose', 1, 'solver', 'sdpt3');

solvesos(FeasibilityConstraints, [], options, [c0;c1;c2;myeps0;myeps1;myeps2])

mono_inv=monolist([parx], 6);
pinv=double(c0')*mono_inv;
sdisplay(clean(pinv,1e-6))
