%computing the range of h, which satisfy max(e)*h<=var_epsilon

var_epsilon=0.1;
L=0.9;
max1=3.16;
max2=2.8;
max3=0.74; 
max_f=[3.7997,2.5937,3.3571];% above parameters are setted based on the results from compute_parameters.m
T=5;
seq=[0.7,0.2,T-0.9];% the sequence of each ODE's execute times, get from the simulation results 
e=zeros(1,3); % error sequence at different time points
for i=1:length(seq)
    if i==1
        e(i)=(max1/2)*((exp(seq(i)*L)-1)/L)+max_f(i);
        
    elseif i==2
        e(i)=exp(seq(i)*L)*e(i-1)+(max3/2)*((exp(seq(i)*L)-1)/L)+max_f(i);
        
    else
        e(i)=exp(seq(i)*L)*e(i-1)+(max2/2)*((exp(seq(i)*L)-1)/L)+max_f(i);
    end
end
disp(['h<=' num2str(var_epsilon/max(e))]); % h<=var_epsilon/max(e)

