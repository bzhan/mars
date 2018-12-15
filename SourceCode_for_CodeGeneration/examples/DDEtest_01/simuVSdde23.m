
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
lags = [1.3];   %delays
tspan = [0,5];   %time bounds

sol=dde23(@ddefun,lags,@history,tspan);  % the dde23 result
[stepsize,times,values,errors] = getStepsize(lags, tspan); % the simulation-based method result
plot(sol.x,sol.y,'-*g',times,values,'-b',times,values+errors,'-r',times,values-errors,'-y');  % plot their result in one figure
title('HCSP vs. SystemC');
xlabel('t');ylabel('y'); 
legend('hcsp','sc','sc-ub','sc-lb'); 

function dydt=ddefun(t,y,Z) % dde function
ylag1=Z(:,1); 
dydt=[y(1)*(1-ylag1(1))]; 

function S=history(t) % history for dde23
S=0.5;

