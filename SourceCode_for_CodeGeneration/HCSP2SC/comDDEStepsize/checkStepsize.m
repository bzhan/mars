%---------------------------------------------------------------------------
% checkStepsize: check whether the stepsize meet the given precision
% return check_h>0: a valid stepsize ensure the error bound meet
% return check_h=-1: the stepsize(h) can not meet the error bound
%---------------------------------------------------------------------------

function  [check_h,times,values,errors] = checkStepsize(dyn,dim,lags,tspan,h,precision,t,y,d)
if nargin ~= 9
    error('checkStepsize:argChk','Wrong number of input arguments');
end
%plot for dim = 2
% figure
% hold all;
% hd = ezplot('y1+y2',[-0.5,1.5]);
% set(hd,'LineColor','r');
% legend(hd,'upper bound of the unsafe set');
% xlabel('S');

n = length(t); % start simulation from the last moment of the history time
m = lags(1)/h; % look backward for m stepsizes
% disp(tspan(end));
while t(end) < tspan(end) && tspan(end)-t(end)>1.0e-4 %the latter exp used for avoiding tspan(end)-t(end)=0 is regared as t(end) < tspan(end)
    tn1 = t(n)+h; % time advanced for one stepsize
    yn1 = dyn(getl(y,n),getl(y,n-m))*h+getl(y,n); % Euler method
    
    % constraint solving, also validated by HySAT.
    obj = @(p) p(1);
    cons1 = @(p) [-p(2);p(2)-h];
    % p(1):e,p(2):t,p(3):x,p(4):u,p(5):f,p(6):g
    if dim == 1
        cons2 = @(p) [(p(3)-getl(y,n,1))^2-getl(d,n)^2; ...,
            (p(4)-getl(y,n-m,1))^2-getl(d,n-m)^2; ...,
            (p(5)-dyn(getl(y,n),getl(y,n-m)))^2-p(1)^2; ...,
            (p(6)-dyn(getl(y,n-m),getl(y,n-2*m)))^2-(1/h*(getl(d,n-m+1)-getl(d,n-m)))^2];
        if n-m <= 1
            cons3 = @(p) [norm(dyn(p(3)+p(5)*p(2),p(4))-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        else
            cons3 = @(p) [norm(dyn(p(3)+p(5)*p(2),p(4)+p(6)*p(2))-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        end  
        
        % p(1):e,p(2):t,p(3):x1,p(4):x2,p(5):u1,p(6):u2,p(7):f1,p(8):f2,p(9):g1,p(10):g2
    elseif dim == 2
        cons2 = @(p) [(p(3)-getl(y,n,1))^2+(p(4)-getl(y,n,2))^2-getl(d,n)^2; ...,
            (p(5)-getl(y,n-m,1))^2+(p(6)-getl(y,n-m,2))^2-getl(d,n-m)^2; ...,
            (p(7)-getl(dyn(getl(y,n),getl(y,n-m))',1))^2+(p(8)-getl(dyn(getl(y,n),getl(y,n-m))',2))^2-p(1)^2; ...,
            (p(9)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',1))^2+(p(10)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',2))^2-(1/h*(getl(d,n-m+1)-getl(d,n-m)))^2];
        if n-m <= 1
            cons3 = @(p) [norm(dyn([p(3)+p(7)*p(2);p(4)+p(8)*p(2)],[p(5);p(6)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        else
            cons3 = @(p) [norm(dyn([p(3)+p(7)*p(2);p(4)+p(8)*p(2)],[p(5)+p(9)*p(2);p(6)+p(10)*p(2)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        end
        
        % p(1):e,p(2):t,p(3):x1,p(4):x2,p(5):x3,p(6):u1,p(7):u2,p(8):u3,p(9):f1,p(10):f2,p(11):f3,p(12):g1,p(13):g2,P(14):g3
    elseif dim == 3
        cons2 = @(p) [(p(3)-getl(y,n,1))^2+(p(4)-getl(y,n,2))^2+(p(5)-getl(y,n,3))^2-getl(d,n)^2; ...,
            (p(6)-getl(y,n-m,1))^2+(p(7)-getl(y,n-m,2))^2+(p(8)-getl(y,n-m,3))^2-getl(d,n-m)^2; ...,
            (p(9)-getl(dyn(getl(y,n),getl(y,n-m))',1))^2+(p(10)-getl(dyn(getl(y,n),getl(y,n-m))',2))^2+(p(11)-getl(dyn(getl(y,n),getl(y,n-m))',3))^2-p(1)^2; ...,
            (p(12)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',1))^2+(p(13)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',2))^2+(p(14)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',3))^2-(1/h*(getl(d,n-m+1)-getl(d,n-m)))^2];
        if n-m <= 1
            cons3 = @(p) [norm(dyn([p(3)+p(9)*p(2);p(4)+p(10)*p(2);p(5)+P(11)*p(2)],[p(6);p(7);p(8)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        else
            cons3 = @(p) [norm(dyn([p(3)+p(9)*p(2);p(4)+p(10)*p(2);p(5)+P(11)*p(2)],[p(6)+p(12)*p(2);p(7)+p(13)*p(2);p(8)+p(14)*p(2)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        end
        
        % p(1):e,p(2):t,p(3):x1,p(4):x2,p(5):x3,p(6):x4,p(7):u1,p(8):u2,p(9):u3,p(10):u4,p(11):f1,p(12):f2,p(13):f3,p(14):f4,p(15):g1,p(16):g2,p(17):g3,p(18):g4
    elseif dim ==4
        cons2 = @(p) [(p(3)-getl(y,n,1))^2+(p(4)-getl(y,n,2))^2+(p(5)-getl(y,n,3))^2+(p(6)-getl(y,n,4))^2-getl(d,n)^2; ...,
            (p(7)-getl(y,n-m,1))^2+(p(8)-getl(y,n-m,2))^2+(p(9)-getl(y,n-m,3))^2+(p(10)-getl(y,n-m,4))^2-getl(d,n-m)^2; ...,
            (p(11)-getl(dyn(getl(y,n),getl(y,n-m))',1))^2+(p(12)-getl(dyn(getl(y,n),getl(y,n-m))',2))^2+(p(13)-getl(dyn(getl(y,n),getl(y,n-m))',3))^2+(p(14)-getl(dyn(getl(y,n),getl(y,n-m))',4))^2-p(1)^2; ...,
            (p(15)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',1))^2+(p(16)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',2))^2+(p(17)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',3))^2+(p(18)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',4))^2-(1/h*(getl(d,n-m+1)-getl(d,n-m)))^2];
        if n-m <= 1
            cons3 = @(p) [norm(dyn([p(3)+p(11)*p(2);p(4)+p(12)*p(2);p(5)+p(13)*p(2);p(6)+p(14)*p(2)],[p(7);p(8);p(9);p(10)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        else
            cons3 = @(p) [norm(dyn([p(3)+p(11)*p(2);p(4)+p(12)*p(2);p(5)+p(13)*p(2);p(6)+p(14)*p(2)],[p(7)+p(15)*p(2);p(8)+p(16)*p(2);p(9)+p(17)*p(2);p(10)+p(18)*p(2)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        end
        % p(1):e,p(2):t,p(3):x1,p(4):x2,p(5):x3,p(6):x4,p(7):x5,p(8):u1,p(9):u2,p(10):u3,p(11):u4,p(12):u5,p(13):f1,p(14):f2,p(15):f3,p(16):f4,p(17):f5,p(18):g1,p(19):g2,p(20):g3,p(21):g4,p(22):g5
    elseif dim ==5
        cons2 = @(p) [(p(3)-getl(y,n,1))^2+(p(4)-getl(y,n,2))^2+(p(5)-getl(y,n,3))^2+(p(6)-getl(y,n,4))^2+(p(7)-getl(y,n,5))^2-getl(d,n)^2; ...,
            (p(8)-getl(y,n-m,1))^2+(p(9)-getl(y,n-m,2))^2+(p(10)-getl(y,n-m,3))^2+(p(11)-getl(y,n-m,4))^2+(p(12)-getl(y,n-m,5))^2-getl(d,n-m)^2; ...,
            (p(13)-getl(dyn(getl(y,n),getl(y,n-m))',1))^2+(p(14)-getl(dyn(getl(y,n),getl(y,n-m))',2))^2+(p(15)-getl(dyn(getl(y,n),getl(y,n-m))',3))^2+(p(16)-getl(dyn(getl(y,n),getl(y,n-m))',4))^2+(p(17)-getl(dyn(getl(y,n),getl(y,n-m))',5))^2-p(1)^2; ...,
            (p(18)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',1))^2+(p(19)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',2))^2+(p(20)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',3))^2+(p(21)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',4))^2+(p(22)-getl(dyn(getl(y,n-m),getl(y,n-2*m))',5))^2-(1/h*(getl(d,n-m+1)-getl(d,n-m)))^2];
        if n-m <= 1
            cons3 = @(p) [norm(dyn([p(3)+p(13)*p(2);p(4)+p(14)*p(2);p(5)+p(15)*p(2);p(6)+p(16)*p(2);p(7)+p(17)*p(2)],[p(8);p(9);p(10);p(11);p(12)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        else
            cons3 = @(p) [norm(dyn([p(3)+p(13)*p(2);p(4)+p(14)*p(2);p(5)+p(15)*p(2);p(6)+p(16)*p(2);p(7)+p(17)*p(2)],[p(8)+p(18)*p(2);p(9)+p(19)*p(2);p(10)+p(20)*p(2);p(11)+p(21)*p(2);p(12)+p(22)*p(2)])-dyn(getl(y,n),getl(y,n-m)))-p(1)];
        end
    end
    
    conseq = [];
    nonlinfcn = @(p)deal([cons1(p);cons2(p);cons3(p)],conseq);
    
    [eee,fval,exitflag,output]=fmincon(obj,[0;0.5*h;getl(y,n)';getl(y,n-m)';dyn(getl(y,n),getl(y,n-m))';dyn(getl(y,n-m),getl(y,n-2*m))'], ...,
        [],[],[],[],[],[],nonlinfcn,optimoptions('fmincon','Display','none'));
    if exitflag >= 0 % the constraint solving is succesfully solved
        e = fval; % error slope
        disp(['The error slope in this simulation is ', num2str(e)]);
        dn1 = getl(d,n)+h*e; % error bound at the next moment
    else  % the constraint solving is not succesfully solved, return an unvalid stepsize h=-1
        h = -1;
        disp('This checkStepsize() procedure is stopped by the computation of the error slope');
        break;
    end
    temp=zeros(1); % record the max error for all dims
    for k = 1:dim
        temp=[temp;abs(max(y(n,k)+getl(d,n),yn1(k)+dn1)-min(y(n,k)-getl(d,n),yn1(k)-dn1))]; % take the whole interval in consideration
        %temp=[temp;abs(getl(d,n)+dn1)]; % consider the simulation points only
    end
    %disp(temp);
    t = [t;tn1];
    y = [y;yn1];
    d = [d;dn1];
    n = n+1;
    if max(temp)>precision % if the maximal error is greater than then precision, the stepsize h is not a valid one  
        h = -1;
        disp('This checkStepsize() procedure is stopped by the error bound constrain');
        break;
    end

end
disp(['In this checkStepsize() procedure, ',num2str(n-2),' simulation steps have been taken']);
result=[t,y,d];
disp('The simulation results (t,y,d) are: ');
disp(result);
check_h=h; % store the result
times=t;
values=y;
errors=d;

%plot for dim = 1

%     subplot(2,3,simNum);
%     hd = plot(t(2:end),y(2:end),'k-',t(2:end),y(2:end)+d(2:end),'K--',t(2:end),y(2:end)-d(2:end),'k--');
%     axis([0,5.2,0.4,1.7]);
%     set(hd(1),'LineWidth',2);
%     set(hd(2),'LineWidth',1.5);
%     set(hd(3),'LineWidth',1.5);
%     hline = refline([0,unsafe(0)]);
%     set(hline,'LineWidth',2);

    %plot for dim = 2
%     curvey = plot(y(2:end,1),y(2:end,2),'g-');
%     if simNum == 1
%         legend(curvey,'numerical solution (S;x)');
%     end
%     circles(y(2:end,1),y(2:end,2),d(2:end));


%-----------------------------------------------------------------------
