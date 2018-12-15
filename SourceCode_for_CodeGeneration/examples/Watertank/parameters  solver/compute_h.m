%computing the range of h, which satisfy max(e)*h<=var_epsilon (Eular method)

var_epsilon=0.2;
L=0.125;
max1=0.145;
max2=0.105; 
max_f=[1.0444,1.1388,1.1652,1.1414,1.1627,1.1427];% above parameters are setted based on the results from compute_parameters.m
T=16;
seq=[2,3,3,3,3,2];% the sequence of each ODE's execute times, get from the simulation results 
e=zeros(1,6); % error sequence at different time points, accordingt to the error bound using Eular method
for i=1:length(seq)
    if i==1
        e(i)=(max1/2)*((exp(seq(i)*L)-1)/L)+max_f(i);
        
    elseif mod(i,2)==0
        e(i)=exp(seq(i)*L)*e(i-1)+(max2/2)*((exp(seq(i)*L)-1)/L)+max_f(i);
        
    else
        e(i)=exp(seq(i)*L)*e(i-1)+(max1/2)*((exp(seq(i)*L)-1)/L)+max_f(i);
    end
end
%disp(e);
disp(['h<=' num2str(var_epsilon/max(e))]); % h<=var_epsilon/max(e)

