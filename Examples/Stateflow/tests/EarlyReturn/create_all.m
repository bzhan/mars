for i = 1:13
    model = "EarlyReturn"+i;
    load_system(model)
    save_system(model, model+".xml", "ExportToXML", true)
    save_system(model, model+"_2018a.slx", "ExportToVersion", "R2018a")
    close_system(model)
end
