%-----------------------------------------------------------------------
% Code the DDEs, the demanded precision, initial stepsize, and the
% initial state.
%-----------------------------------------------------------------------
function [stepsize,t,y,d] = getStepsize(lags, tspan)

%% initialization
dim = 1;   %dimension of the system
delta = 0;   %initial diameter
precision=0.5; % the precision bound
init=0.5; % initial state
h = lags;   %initial stepsize of the simulation

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
%disp(stepsize);

%% DDE expression, y for the current state and u for the past state (with delay lags)
function yp = dyn(y,u)
yp = [y(1)*(1-u(1))];

%-----------------------------------------------------------------------
