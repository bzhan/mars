function gt = getl(list,index,col)

if index < 1
    gt = list(1,:);
elseif index > length(list)
    gt = list(end,:);
else
    gt = list(index,:);
end

if nargin == 3
    gt = gt(col);
end