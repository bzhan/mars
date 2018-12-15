% estimate parameters that used for calculating the step size h
clear all;

% get the upper bound of epsilon, by executing hcs.mdl (the period of
% the controller is 0.128 and the period of plant is 0.001) for a bounded time.
boundedTime=10;
out = sim('hcs','StopTime', num2str(boundedTime)); 
output=[out.get('yout').time,out.get('yout').signals(1).values,out.get('yout').signals(2).values,out.get('yout').signals(3).values,out.get('yout').signals(4).values]; %get output with time 
lower_bound=3000;
up_bound=3000;
res0=1000;
period=0.128;
output_1=[];
n=0;
for i=1:size(output(:,1))%get all output value at n*period time points
    if (output(i,1)-period*n)==0 || abs(output(i,1)-period*n)<1e-12
        n=n+1;
        output_1=[output_1,output(i,2)];
    end
end
for i=1:size(output_1(:,1))
    x1=output_1(i,2);
    res0=min(res0,min(abs(x1-up_bound),abs(x1-lower_bound)));
end
    disp(['epsilon<=' num2str(res0)]);

% get the lower bound of L.
res=0;
for i=1:size(output(:,1))-1 %two fors, take all pairs of values into consideration
    x1=output(i,2);%Fc
    x2=output(i,3);%m
    x3=output(i,4);%v
    x4=output(i,5);%r
    for j=i+1:size(output(:,1))
        x1_p=output(j,2);%Fc_p
        x2_p=output(j,3);%m_p
        x3_p=output(j,4);%v_p
        x4_p=output(j,5);%r_p
        temp_1=abs(x1/x2-x1_p/x2_p);
        temp_2=abs(x1-x1_p)/2548;
        temp_3=abs(x3-x3_p);
        temp_4=max(abs(x1-x1_p),abs(x2-x2_p));
        temp_5=max(abs(x3-x3_p),abs(x4-x4_p));
        temp=max(temp_1,max(temp_2,temp_3))/max(temp_4,temp_5);%according to the definition of L
        res=max(res,temp);
    end
end
    disp(['L>=' num2str(res)]);

% % get the lower bound of each ODE's two-order derivative, using the execution of roomheating_dense (the period of
% % the controller is 0.001) for a bounded time.    
res1=0;
max_f=[];%list of maximal first-order derivative for ODEs
max_f_1=0;%record the max value of the first-order derivative for ODE1 during different intervals
for i=2:size(output(:,1))
    x1=output(i,2);%Fc
    x2=output(i,3);%m
    x3=output(i,4);%v
    res1=max(res1,max(abs(x1/x2-1.622),abs((x1/x2)*(x1/x2)/2548))); 
    temp_1=max(abs(x3),abs(x1/x2-1.622));
    temp_2=max(temp_1,abs(x1/2548));
    max_f_1=max(max_f_1,temp_2);
end
max_f=[max_f,max_f_1];
disp(['max1>=' num2str(res1)]);
disp(['max_f=' num2str(max_f)]);
