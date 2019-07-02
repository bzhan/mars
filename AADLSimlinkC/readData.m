dataAir = textread('data/737301/air.txt','%n');
dataHeat = textread('data/737301/heat.txt','%n');
len = size(dataHeat);
heat = [];
for i=1:len
    if mod(i,3)==0
        j=i/3;
        heat(j) = dataHeat(i);
    end
end
hold on;
plot(dataAir,'.')
plot(heat,'-')
%plot(heat)