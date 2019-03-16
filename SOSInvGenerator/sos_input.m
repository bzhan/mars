sdpvar pary parx;
sdpvar myeps0 myeps1 myeps2;

lambda1 = .5;
lambda2 = 1;

tol0 = 1e-6;
tol1 = 1e-6;
tol2 = 1e-6;

[inv, c0] = polynomial([pary parx], 4);
[s1, c1] = polynomial([pary parx], 2);
[s2, c2] = polynomial([pary parx], 2);
[s3, c3] = polynomial([pary parx], 2);

f0 = sos(-inv - s1 * (((1)/(2))- parx^2 )- s2 * (((1)/(3))- pary^2 ) - myeps0);

f1 = sos(inv - s3 * (-((8)-(parx- (4)*pary ))) - myeps1);

flow0 = [(((((0)-parx)- (1117)*pary /(500) )+ (439)* pary^3 /(200) )- (333)* pary^5 /(500) ); (((parx+ (617)*pary /(500) )- (439)* pary^3 /(200) )+ (333)* pary^5 /(500) )];
dinv0 = [jacobian(inv,parx), jacobian(inv,pary)];
lie0 = dinv0 * flow0;
f2 = sos(-lie0 - lambda1 * inv - myeps2);

FeasibilityConstraints=[f0,f1,f2,sos(s1),sos(s2),sos(s3),myeps0>=tol0,myeps1>=tol1,myeps2>=tol2];

options=sdpsettings('verbose', 1, 'solver', 'mosek');

sos_ans = solvesos(FeasibilityConstraints, [], options, [c0;c1;c2;c3;myeps0;myeps1;myeps2])

if sos_ans.problem == 0
  mono_inv=monolist([pary parx], 4);
  pinv=double(c0')*mono_inv;
  sdisplay(clean(pinv,1e-6))
else
  fprintf("error\n")
end

