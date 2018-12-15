
function simulation
clear;
clc;
% lags=[1]; tspan=[0,15];    %dde23 example
% sol=dde23(@ddefun,lags,@history,tspan); 
% plot(sol.x,sol.y); 
% title('ddefun');xlabel('t');ylabel('y'); 
% legend('y_1','y_2','y_3','y_4',2); 
% 
% function dydt=ddefun(t,y,Z) 
% ylag1=Z(:,1); 
% 
% 
% dydt=[(-0.5)*y(1)-2*y(2)+ylag1(3) 
% 2*y(1)-0.5*y(2)+ylag1(4) 
% (-0.5)*y(3)-0.5*y(4)+ylag1(1) 
% 0.5*y(3)-0.5*y(4)+ylag1(2)]; 
% 
% function S=history(t) 
% S=ones(4,1);

lags = [0.1];   %delays
tspan = [0,10];   %time bounds

% other parameters of the system
p=1; % period length for each DDEs
lb=4.1; % condition bound
ub=5.9;
running=1; % recording the last execution

[stepsize,times,values,errors] = getStepsize(lags, tspan, p, lb, ub); %the simulation-based method

options = ddeset('MaxStep',stepsize);
vareps=[];
for k=1:tspan(end)/p  % dde23 result (similar to the process of the simulation-based method)
    tspan_temp=[(k-1)*p,k*p];
    if k==1
        sol=dde23(@ddefun1,lags,@history,tspan_temp,options);
        running=1;
    else
        if sol.y(end)>=ub
            sol=dde23(@ddefun2,lags,sol,tspan_temp,options);
            running=2;
            vareps=[vareps;abs(sol.y(end)-ub)];
        elseif sol.y(end)<=lb
            sol=dde23(@ddefun1,lags,sol,tspan_temp,options);
            running=1;
            vareps=[vareps;abs(sol.y(end)-lb)];
        else
            if running==1
                sol=dde23(@ddefun1,lags,sol,tspan_temp,options);
                vareps=[vareps;abs(sol.y(end)-ub)];
            else
                sol=dde23(@ddefun2,lags,sol,tspan_temp,options);
                vareps=[vareps;abs(sol.y(end)-lb)];
            end
        end
    end
end
disp(['The varepsilon is ',num2str(min(vareps))]);
%plot(sol.x,sol.y,'-g');
%plot(sol.x,sol.y,'-g',times,values,'-r'); % compare their results in one figure
plot(sol.x,sol.y,'-g',times,values,'-*b',times,values+errors,'-r',times,values-errors,'-y'); % compare their results in one figure
%title('HCSP vs. SystemC');
xlabel('t');ylabel('y'); 
legend('d-HCSP','d-SC','d-SC+d','d-SC-d'); 

function dydt1=ddefun1(t,y,Z) %DDE_1
Qmax=2;
pai=3.14;
r=0.18;
g=9.8;
ylag1=Z(:,1); 
dydt1=[Qmax-pai*r*r*sqrt(g*(y(1)+ylag1(1)))]; 

function S=history(t) %DDE_1 initial values
S=4.5;

function dydt2=ddefun2(t,y,Z) %DDE_2
Qmax=2;
pai=3.14;
r=0.18;
g=9.8;
ylag1=Z(:,1); 
dydt2=[-pai*r*r*sqrt(g*(y(1)+ylag1(1)))]; 

