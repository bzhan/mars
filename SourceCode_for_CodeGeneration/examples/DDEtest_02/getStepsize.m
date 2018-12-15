%-----------------------------------------------------------------------
% Code the DDEs, the associated delays, integration interval, initial
% set of constant functions, and a unsafe set in the following segment.
%-----------------------------------------------------------------------
function [stepsize,t,y,d] = getStepsize(lags, tspan)

%% initialization
dim = 2;   %dimension of the system
delta = 0;   %initial diameter
precision=0.5; % erro bound
init = [1,0.5];   %initial state
h = lags;   %stepsize of the simulation

t = [tspan(1)-h;tspan(1)]; % time sequence
y = [init;init]; % simulation points
d = [0;delta];  % error sequence 
tic;
%% compute the stepsize and corresponding time points, state values and error sequence
[stepsize,times,values,errors,failed_com] = comStepsize(@dyn,dim,lags,tspan,h,precision,t,y,d);
toc;
if stepsize>0 % valid stepsize, store the results (used for simVSdde23) and write them into the 'simResult.txt' file (used for code generation).
   t=times;
   y=values;
   d=errors;
   fid=fopen('./simResult.txt','w');
   fprintf(fid,'%s','times=');
   fprintf(fid,'%f,',times); 
   fprintf(fid,';\n%s','values=');
   if dim>1
       for a=1:size(values,1)
           fprintf(fid,'%s','(');
           for b=1:dim
               if b==dim
                   fprintf(fid,'%f),',values(a,b));
               else
                   fprintf(fid,'%f,',values(a,b));
               end
           end
       end
   else
       fprintf(fid,'%f,',values);
   end
   fprintf(fid,';\n%s','errors=');
   fprintf(fid,'%f,',errors);
   fclose(fid);
end

function yp = dyn(y,u)
yp = zeros(1,2);
yp(1) = 1-y(1)-2*exp(1)*y(1)/(1+y(1))*y(2);
yp(2) = exp(-0.9)*2*exp(1)*u(1)/(1+u(1))*u(2)-y(2);


%-----------------------------------------------------------------------
