%---------------------------------------------------------------------------
% comStepsize: a tool for computing the stepsize which ensures the error 
% between the DDE and its discretization is bounded by a given precision
% within all time intervals [t(i),t(i+1)]. DDEs have the form 
% x'(t) = f(x(t),x(t-r)).
%
% return:
% stepsize>0: a valid stepsize ensure the error bound meet
% stepsize=-1: can not find large enough stepsize to meet the error
% bound
%---------------------------------------------------------------------------

function [stepsize,times,values,errors,failed] = comStepsize(dyn,dim,lags,tspan,h,precision,t,y,d)
if nargin ~= 9
    error('comStepsize:argCss','Wrong number of input arguments');
end
n=0; % store the times for finding a valid stepsize
failed=0; % whether a valid stepsize got or not
while(abs(h)>1.0e-10) % lower bound of the stepsize
    [stepsize,times,values,errors] = checkStepsize(dyn,dim,lags,tspan,h,precision,t,y,d); % check whether the current stepsize h satisfy the precision
    if stepsize<0 % unvalid stepsize, choose a smaller one
        h=h/2;
        n=n+1;
    else          % valid stepsize found
        n=n+1;
        break;
    end
end
disp(['CheckStepsize() is executed for ',num2str(n),' times']);
stepsize=h;
if abs(h)<=1.0e-10 % the stepsize is too small
    disp('The stepsize goes too small...');
    failed=1;
    stepsize=-1;
else   % the stepsize is ok
    disp(['The stepsize satisfy the precison is ',num2str(stepsize)]);
end

