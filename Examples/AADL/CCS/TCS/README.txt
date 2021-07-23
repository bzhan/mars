The models of the CCS are stored in a JSON format, such as model_1bus.json which describes the case containing 1 bus. We can change the configuration of the CCS freely by modifying the JSON file.

The program json2hcsp_test.py serves as the translator that transforms a JSON file of the CCS into files of HCSP modules. You can reset the path that links to the JSON file to be loaded through modifying the line 78 of json2hcsp.py. Before running json2hcsp.py, you need to
(1) Set your working directory to "... /mars/"
(2) Modify the JSON file to be loaded if necessary
(3) Run json2hcsp_test.py, then the files of HCSP modules will be generated, where the file system.txt is the main file showing the whole system is the parallel composition of subcomponents.


If you want to run the generate HCSP files to obtain the simulation results, you need to
(1) Install Node.js
(2) Run the server: "... /mars/ss2hcsp/server/simulator_server.py"
(3) Switch into the directory mars/hcsp_simulator and run "npm start"
(4) Open an Web brower and search "http://localhost:3000"
(5) If success, you will see the graphical interface of our HCSP simulator
(6) Create the file import_path.txt in the directory mars/ss2hcsp, and type into the full path "... /mars/Examples/AADL/CCS/TCS" where the main file system.txt lies in.
(7) Back to the graphical interface, click the button "Read HCSP File" to load the file system.txt generated before. If success, you will see the subcomponents of the system and their details.
(8) Set the number of steps and the number of events you want to show (Showing), and then click the left triangle to run. The running may take some time and after that, you will see the graphical results of some components by click "Show graph".
