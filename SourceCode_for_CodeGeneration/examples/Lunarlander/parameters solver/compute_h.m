%computing the range of h, which satisfy max(e)*h<=var_epsilon

var_epsilon=0.05;
L=0.0003;
max1=0.0011; 
max_f=2;% above parameters are setted based on the results from compute_parameters.m
T=10;
seq=repmat(0.128,1,78);% the sequence of each ODE's execute times, get from the simulation results 
e=zeros(1,78); % error sequence at different time points
for i=1:length(seq)
    if i==1
        e(i)=(max1/2)*((exp(seq(i)*L)-1)/L)+max_f;
    else
        e(i)=exp(seq(i)*L)*e(i-1)+(max1/2)*((exp(seq(i)*L)-1)/L)+max_f;
    end
end
disp(['h<=' num2str(var_epsilon/max(e))]); % h<=var_epsilon/max(e)

