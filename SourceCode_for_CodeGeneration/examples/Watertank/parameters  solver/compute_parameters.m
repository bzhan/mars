% estimate parameters that used for calculating the step size h
clear all;

% get the upper bound of epsilon, by executing waterTank.mdl (the period of
% the controller is 1 and the period of plant is 0.001) for a bounded time.
boundedTime=16;
out = sim('waterTank','StopTime', num2str(boundedTime)); 
output=[out.get('yout').time,out.get('yout').signals(1).values]; %get output with time 
lower_bound=4.1;
up_bound=5.9;
res0=1000;
period=1;
output_1=[];
n=0;
for i=1:size(output(:,1))%get all output value at integral time points
    if (output(i,1)-period*n)==0 || abs(output(i,1)-period*n)<1e-12
        n=n+1;
        output_1=[output_1,output(i,2)];
    end
end
for i=2:length(output_1)
    x1=output_1(i);
    if(x1-output_1(i-1)>=0)%condition_1
        res0=min(res0,abs(x1-up_bound));%record the minimal value
        %disp(res);
    elseif(x1-output_1(i-1)<0 )%condition_2
        res0=min(res0,abs(x1-lower_bound));
        %disp(res);       
    end
end
    disp(['epsilon<=' num2str(res0)]);

% get the lower bound of L
res=0;
pi=3.14;
r=0.18;
g=9.8;
for i=1:size(output(:,1))-1 %two fors, take all pairs of values into consideration
    x1=output(i,2);%d
    for j=i+1:size(output(:,1))
        x1_p=output(j,2);
        temp=pi*r*r*sqrt(2*g)/(sqrt(x1)+sqrt(x1_p));%according to the definition of L
        res=max(res,temp);
    end
end
    disp(['L>=' num2str(res)]);
 
% get the lower bound of each ODE's two-order derivative and upper bound of
% ODE's first-order derivative within different intervals
res1=0;
res2=0;
max_f=[];%list of maximal first-order derivative for ODEs
max_f_1=0;%record the max value of the first-order derivative for ODE1 during different intervals
max_f_2=0;%record the max value of the first-order derivative for ODE2 during different intervals
res_size=length(output(:,1))-1;
for i=2:size(output(:,1))-1
    x1=output(i,2);
    if(x1-output(i-1,2)>=0)% executing ODE_1 
        res1=max(res1,abs(pi*r*r*sqrt(2*g)*(pi*r*r*sqrt(g/2)-sqrt(1/x1))));   
        max_f_1=max(max_f_1,abs(2-pi*r*r*sqrt(2*g*x1)));
        if(x1-output(i-1,2)>=0&&x1-output(i+1,2)>=0) % at the inflection point, record the max value in max_f
            max_f=[max_f,max_f_1];
            max_f_1=0;
        end
        if(i==res_size)% at the last point, need record
            max_f=[max_f,max_f_1];
        end
    elseif(x1-output(i-1,2)<0) % executing ODE_2 
        res2=max(res2,pi^2*r^4*g);
        max_f_2=max(max_f_2,abs(pi*r*r*sqrt(2*g*x1)));
        if(x1-output(i-1,2)<0&&x1-output(i+1,2)<0)% at the inflection point, record the max value in max_f
            max_f=[max_f,max_f_2];
            max_f_2=0;
        end
        if(i==res_size)% at the last point, need record
            max_f=[max_f,max_f_2];
        end
    end
end
disp(['max1>=' num2str(res1)]);
disp(['max2>=' num2str(res2)]);
disp(['max_f=' num2str(max_f)]);
