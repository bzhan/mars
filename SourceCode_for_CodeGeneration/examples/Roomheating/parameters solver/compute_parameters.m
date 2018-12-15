% estimate parameters that used for calculating the step size h
clear all;

% get the upper bound of epsilon, by executing roomheating.mdl (the period of
% the controller is 0.1 and the period of plant is 0.0001) for a bounded time.
boundedTime=5;
out = sim('roomheating','StopTime', num2str(boundedTime)); 
output=[out.get('yout').time,out.get('yout').signals(1).values,out.get('yout').signals(2).values]; %get output with time 
res0=1000;
period=0.1;
output_1=[];
n=0;
for i=1:size(output(:,1))%get all output value at integral time points
    if (output(i,1)-period*n)==0 || abs(output(i,1)-period*n)<1e-12
        n=n+1;
        output_1=[output_1;output(i,:)];
    end
end
for i=2:size(output_1(:,1))
    x1=output_1(i,2);
    x2=output_1(i,3);
    if(x1-output_1(i-1,2)>0 && x2<=8 && (x1-x2)>=0.5)%condition_1
        res0=min(res0,min(8-x2,x1-x2-0.5));%record the minimal value
        %disp(res);
    elseif(x2-output_1(i-1,3)>0 && x1<=8 && (x2-x1)>=0.5)%condition_2
        res0=min(res0,min(8-x1,x2-x1-0.5));
        %disp(res);       
    elseif(x1-output_1(i-1,2)>0 && x1<=10)%condition_3
        res0=min(res0,10-x1);
        %disp(res);    
    elseif(x2-output_1(i-1,3)>0 && x2<=10)%condition_4
        res0=min(res0,10-x2);
        %disp(12-x2);
    elseif(x1>=12)%condition_5
        res0=min(res0,x1-12);
        %disp(res);
    elseif(x2>=12)%condition_6
        res0=min(res0,x2-12);
        %disp(res);
    end
end
    disp(['epsilon<=' num2str(res0)]);

% get the lower bound of L
res=0;
for i=1:size(output(:,1))-1 %two fors, take all pairs of values into consideration
    x1=output(i,2);
    x2=output(i,3);
    for j=i+1:size(output(:,1))
        x1_p=output(j,2);
        x2_p=output(j,3);
        temp_1=abs(0.45*(x1_p-x1)+0.25*(x2-x2_p));
        temp_2=abs(0.25*(x1-x1_p)+0.65*(x2_p-x2));
        temp=max(temp_1,temp_2)/max(abs(x1-x1_p),abs(x2-x2_p));%according to the definition of L
        res=max(res,temp);
    end
end
    disp(['L>=' num2str(res)]);

% get the lower bound of each ODE's two-order derivative and upper bound of
% ODE's first-order derivative within different intervals
res1=0;
res2=0;
res3=0;
max_f=[];%list of maximal first-order derivative for ODEs
max_f_1=0;%record the max value of the first-order derivative for ODE1 during different intervals
max_f_3=0;%record the max value of the first-order derivative for ODE3 during different intervals
max_f_2=0;%record the max value of the first-order derivative for ODE2 during different intervals
res_size=length(output(:,1))-1;
for i=2:size(output(:,1))-1
    x1=output(i,2);
    x2=output(i,3);
    if(x1-output(i-1,2)>0)% executing ODE_1 
        res1=max(res1,max(abs(0.265*x1-0.275*x2-2.46),abs(0.485*x2-0.275*x1+1.06)));   
        max_f_1=max(max_f_1,max(abs(0.25*x2-0.45*x1+0.8+5),abs(0.25*x1-0.65*x2+0.6)));
        if(x1-output(i-1,2)>0&&x1-output(i+1,2)>0) % at the inflection point, record the max value in max_f
            max_f=[max_f,max_f_1];
            max_f_1=0;
        end
        if(i==res_size)% at the last point, need record
            max_f=[max_f,max_f_1];
        end
    elseif(x2-output(i-1,3)>0)% executing ODE_2 
        res2=max(res2,max(abs(0.265*x1-0.275*x2+1.04),abs(0.485*x2-0.275*x1-3.44)));
        max_f_2=max(max_f_2,max(abs(0.25*x2-0.45*x1+0.8),abs(0.25*x1-0.65*x2+0.6+5)));
        if(x2-output(i-1,3)>0&&x2-output(i+1,3)>0)% at the inflection point, record the max value in max_f
            max_f=[max_f,max_f_2];
            max_f_2=0;
        end
        if(i==res_size)% at the last point, need record
            max_f=[max_f,max_f_2];
        end
    else % executing ODE_3 
        res3=max(res3,max(abs(0.265*x1-0.275*x2-0.21),abs(0.485*x2-0.275*x1-0.19)));
        max_f_3=max(max_f_3,max(abs(0.25*x2-0.45*x1+0.8),abs(0.25*x1-0.65*x2+0.6)));
        if(x1-output(i+1,3)<0||x2-output(i+1,3)<0)% at the inflection point, record the max value in max_f
            max_f=[max_f,max_f_3];
            max_f_3=0;
        end
        if(i==res_size)% at the last point, need record
            max_f=[max_f,max_f_3];
        end
    end
end
    disp(['max1>=' num2str(res1)]);
    disp(['max2>=' num2str(res2)]);
    disp(['max3>=' num2str(res3)]);
    disp(['max_f=' num2str(max_f)]);
