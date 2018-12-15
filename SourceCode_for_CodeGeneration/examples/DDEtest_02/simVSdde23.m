
function simulation
clear;
clc;
% lags=[1]; tspan=[0,15];
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


%% initialization
lags = [0.9];   %delays
tspan = [0,8];   %time bounds

sol=dde23(@ddefun,lags,@history,tspan);  % the dde23 result
[stepsize,times,values,errors] = getStepsize(lags, tspan); % the simulation-based method result
plot(sol.x,sol.y,times,values);  % plot their result in one figure
title('HCSP vs. SystemC');
xlabel('t');ylabel('y'); 
legend('hcsp-y1','hcsp-y2','sc-y1','sc-y2'); 

function dydt=ddefun(t,y,Z) % dde function
ylag1=Z(:,1); 
dydt=[1-y(1)-2*exp(1)*y(1)/(1+y(1))*y(2)
    exp(-0.9)*2*exp(1)*ylag1(1)/(1+ylag1(1))*ylag1(2)-y(2)]; 
function S=history(t) % history for dde23
S=[1,0.5];

