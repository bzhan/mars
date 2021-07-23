models = ["DSM1", "DSM2", "DSM3", "DSM4", "DSM5", "DSM6"];

for i = 1:length(models)
    model = models(i);
    load_system(model)
    save_system(model, model+".xml", "ExportToXML", true)
    save_system(model, model+"_2018a.slx", "ExportToVersion", "R2018a")
    close_system(model)
end
