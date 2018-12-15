%-----------------------------------------------------------------------
% Code the DDEs and other parameters.
%-----------------------------------------------------------------------
function [stepsize,t,y,d] = getStepsize(lags, tspan, p, lb, ub)

%% initialization
dim = 1;   %dimension of the system
delta = 0;   %initial diameter
precision=0.2; % erro bound
init=4.5; % initial state
h = lags(1);   %stepsize of the simulation
DDE_num=2; % the number of DDE

% other parameters of the system

t = [tspan(1)-h;tspan(1)]; % time sequence
failed=0; % whether can find a valid stepsize to satisfy the precison for the whole time span (multiple DDEs are executed)

y_DDE1 = []; % initilize the simulation values of DDE1
y_DDE2 = []; % initilize the simulation values of DDE2
tic;
%% stepsize computation
while t(end)<tspan(end) && tspan(end)-t(end)>1.0e-4% for the whole execution time
    t = [tspan(1)-h;tspan(1)]; % initilize the time sequence
    y = [init;init]; % initilize the simulation values
    d = [0;delta];  % initilize the error sequence 
    running=1; % identify which DDE was executed during the first period
    
    y_DDE1 = []; % initilize the simulation values of DDE1
    y_DDE2 = []; % initilize the simulation values of DDE2
    
    if failed==1 % can not find valid stepsize for the whole tspan
        disp('The stepsize goes too small...');
        break;
    end
    for k=1:tspan(end)/p % check for every period
        tspan_temp=[(k-1)*p:k*p]; % current time span for p length
        if k==1 % the initial execution (run DDE_1 dyn1)
            [stepsize,times,values,errors,failed_com] = comStepsize(@dyn1,dim,lags,tspan_temp,h,precision,t,y,d); % com the result on this period
            if failed_com==1 % computation for the fisrt DDE is failed (can not find a valid stepsize), the whole process failed
                failed=1;
                break;
            else            % otherwise, record the result and goes on
                h=stepsize;
                t=times;
                y=values;
                d=errors;
                y_DDE1=[y_DDE1;values((p/h)*(k-1)+3:(p/h)*k+2,:)];% cut the values for DDE_1
            end
        else  % for the periods after the first one
            if y(end)>=ub % the condition for choosing which DDE to execute                
                [stepsize,times,values,errors] = checkStepsize(@dyn2,dim,lags,tspan_temp,h,precision,t,y,d); % for DDE_2
                if stepsize<0 % the current stepsize h is not valid, choose a smaller one
                    h=h/2;
                    break;
                else   % otherwise, record the result
                    t=times;
                    y=values;
                    d=errors;
                    running=2;
                    y_DDE2=[y_DDE2;values((p/h)*(k-1)+3:(p/h)*k+2,:)];
                end
            elseif y(end)<=lb % the condition for choosing which DDE to execute                
                [stepsize,times,values,errors] = checkStepsize(@dyn1,dim,lags,tspan_temp,h,precision,t,y,d);% for DDE_1
                if stepsize<0
                    h=h/2;
                    break;
                else
                    t=times;
                    y=values;
                    d=errors;
                    running=1;
                    y_DDE1=[y_DDE1;values((p/h)*(k-1)+3:(p/h)*k+2,:)];
                end
            else     % the condition for choosing which DDE to execute, according to the last running
                if running==1                    
                    [stepsize,times,values,errors] = checkStepsize(@dyn1,dim,lags,tspan_temp,h,precision,t,y,d);
                    if stepsize<0
                        h=h/2;
                        break;
                    else
                        t=times;
                        y=values;
                        d=errors;
                        y_DDE1=[y_DDE1;values((p/h)*(k-1)+3:(p/h)*k+2,:)];
                    end
                else                   
                    [stepsize,times,values,errors] = checkStepsize(@dyn2,dim,lags,tspan_temp,h,precision,t,y,d);
                    if stepsize<0
                        h=h/2;
                        break;
                    else
                        t=times;
                        y=values;
                        d=errors;
                        y_DDE2=[y_DDE2;values((p/h)*(k-1)+3:(p/h)*k+2,:)];
                    end  
                end
            end
        end
    end
end
toc;
if h>1.0e-10 % write the result into a file (used for code generation)
   fid=fopen('./simResult.txt','w');
   fprintf(fid,'%s','times=');
   fprintf(fid,'%f,',t); 
   fprintf(fid,';\n%s','values=');
   if dim>1
       for a=1:size(y,1)
           fprintf(fid,'%s','(');
           for b=1:dim
               if b==dim
                   fprintf(fid,'%f),',y(a,b));
               else
                   fprintf(fid,'%f,',y(a,b));
               end
           end
       end
   else
       fprintf(fid,'%f,',y);
   end
   fprintf(fid,';\n%s','errors=');
   fprintf(fid,'%f,',d);
   
   if size(y_DDE1,1)>1% write the result of DDE1 into the file 
       fprintf(fid,';\n%s','values_DDE1=');
       if dim>1
           for a=1:size(y_DDE1,1)
               fprintf(fid,'%s','(');
               for b=1:dim
                   if b==dim
                       fprintf(fid,'%f),',y_DDE1(a,b));
                   else
                       fprintf(fid,'%f,',y_DDE1(a,b));
                   end
               end
           end
       else
           fprintf(fid,'%f,',y_DDE1);
       end
   end
   
   if size(y_DDE2,1)>1% write the result of DDE2 into the file 
       fprintf(fid,';\n%s','values_DDE2=');
       if dim>1
           for a=1:size(y_DDE2,1)
               fprintf(fid,'%s','(');
               for b=1:dim
                   if b==dim
                       fprintf(fid,'%f),',y_DDE2(a,b));
                   else
                       fprintf(fid,'%f,',y_DDE2(a,b));
                   end
               end
           end
       else
           fprintf(fid,'%f,',y_DDE2);
       end
   end
   fclose(fid);
end
%disp(stepsize);
%% DDE expression, y for the current state and u for the past state (with delay lags)
function yp1 = dyn1(y,u) % DDE_1
Qmax=2;
pai=3.14;
r=0.18;
g=9.8;
yp1 = [Qmax-pai*r*r*sqrt(g*(y(1)+u(1)))];

function yp2 = dyn2(y,u)% DDE_2
Qmax=2;
pai=3.14;
r=0.18;
g=9.8;
yp2 = [-pai*r*r*sqrt(g*(y(1)+u(1)))];
%-----------------------------------------------------------------------
