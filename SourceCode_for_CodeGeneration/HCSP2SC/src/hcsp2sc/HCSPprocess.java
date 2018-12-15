package hcsp2sc;
import java.util.ArrayList;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

import hcsp2sc.ODE;
import hcsp2sc.Constructor;
import hcsp2sc.Constructor.constructorType;

public class HCSPprocess {
	public static ArrayList<ArrayList<Constructor>> processes= new ArrayList<ArrayList<Constructor>>();//store all processes
	public static ArrayList<String> parallelProcesses= new ArrayList<String>();//only store processes in parallel
	public static ArrayList<String> variablesDef= new ArrayList<String>();//all variables definition
	public static ArrayList<String> channelsDef= new ArrayList<String>();//all channels definition
	public static ArrayList<String> constantsDef= new ArrayList<String>();//all constants definition
	public static String systemName;
	
	public static ArrayList<ArrayList<Constructor>> getProcess(String HCSPLoc)
	{
		// open and read HCSPLoc, get sub_processes and add them into process (constructors are separated by ;)......
		try {
			BufferedReader input=new BufferedReader(new FileReader(HCSPLoc));
			String data="",hcspString="";
			while((data=input.readLine())!=null)
			{
				hcspString+=data;
			}
			//System.out.println(hcspString);
			processes=getContructors(hcspString);
			input.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return processes;
	}
	
	public static ArrayList<ArrayList<Constructor>> getContructors(String hcspString)
	{
		if (hcspString.indexOf("systemDef")!=-1)
		{
			systemName=hcspString.substring(hcspString.indexOf("systemDef")+9,hcspString.indexOf("::=")).replaceAll(" ","");
			String temp=hcspString.substring(hcspString.indexOf("::=")+3, hcspString.indexOf("variableDef"));
			temp=temp.replaceAll(" ", "").replaceAll(";", "");
			//System.out.println(temp);
			String[] parallels=temp.split("\\|\\|");//parallel processes names
			for(int i=0;i<parallels.length;i++)
			{
				parallelProcesses.add(parallels[i]);
				//System.out.println(parallelProcesses.get(i));
			}
			hcspString=hcspString.substring(hcspString.indexOf("variableDef"));//only the definition of variables, channels and processes
			String[] allProcesses=hcspString.split("processDef");//split by key words processDef
			
			String varString,chaString,conString;
			temp = allProcesses[0].replaceAll(" ","");
			if (temp.indexOf("channelDef")!=-1)
			{
				if (temp.indexOf("constantDef")!=-1)
				{
					varString=temp.substring(temp.indexOf("::=")+3,temp.indexOf("channelDef"));
					temp=temp.substring(temp.indexOf("channelDef"));
					chaString=temp.substring(temp.indexOf("::=")+3,temp.indexOf("constantDef"));
					temp=temp.substring(temp.indexOf("constantDef"));
					conString=temp.substring(temp.indexOf("::=")+3);
				}
				else
				{
					varString=temp.substring(temp.indexOf("::=")+3,temp.indexOf("channelDef"));
					temp=temp.substring(temp.indexOf("channelDef"));
					chaString=temp.substring(temp.indexOf("::=")+3);
					conString="";
				}
			}
			else
			{
				if (temp.indexOf("constantDef")!=-1)
				{
					varString=temp.substring(temp.indexOf("::=")+3,temp.indexOf("constantDef"));
					temp=temp.substring(temp.indexOf("constantDef"));
					conString=temp.substring(temp.indexOf("::=")+3);
					chaString="";
				}
				else
				{
					varString=temp.substring(temp.indexOf("::=")+3);
					conString=chaString="";
				}
			}
			if (varString.length()>0)
			{
				String[] vars=varString.split(";");
				for (int i=0;i<vars.length;i++)
				{
					variablesDef.add(vars[i]);
				}
			}
			if (chaString.length()>0)
			{
				String[] chas=chaString.split(";");
				for (int i=0;i<chas.length;i++)
				{
					channelsDef.add(chas[i]);
				}
			}
			if (conString.length()>0)
			{
				String[] cons=conString.split(";");
				for (int i=0;i<cons.length;i++)
				{
					constantsDef.add(cons[i]);
				}
			}
			/*test
			for(int i=0;i<variablesDef.size();i++) System.out.println(variablesDef.get(i));
			for(int i=0;i<channelsDef.size();i++) System.out.println(channelsDef.get(i));
			for(int i=0;i<constantsDef.size();i++) System.out.println(constantsDef.get(i));*/

			String procName;//name for each process
			for(int i=1;i<allProcesses.length;i++)//for every process(start from index one), get its name and constructors
			{
				//System.out.println(allProcesses[i]);
				ArrayList<Constructor> processConstructors=new ArrayList<Constructor>();//constructors contained in the process
				String[] processTemp1=allProcesses[i].split("::=");//name split with constructors
				procName=processTemp1[0].replaceAll(" ", "");//get name
                processConstructors.add(new Constructor(constructorType.PROC,procName));//add to the first place of list processConstructors
                //System.out.println(processConstructors.get(0).getContent());
                String[] processTemp2=processTemp1[1].split(";");//get constructors using the split symbol ";"
                for(int j=0;j<processTemp2.length;j++)
                {
                	//for different kind of constructors, add it into processConstructors
                	if(processTemp2[j].contains("SKIP")&&!processTemp2[j].contains("if")&&!processTemp2[j].contains("then"))
                		processConstructors.add(new Constructor(constructorType.SKIP,processTemp2[j].replaceAll(" ", "")));
                	else if(processTemp2[j].contains("=")&&!processTemp2[j].contains("if")&&!processTemp2[j].contains("then")&&!processTemp2[j].contains("DOT("))
                		processConstructors.add(new Constructor(constructorType.ASSI,processTemp2[j].replaceAll(" ", "")));
                	else if(processTemp2[j].contains("WAIT("))
                		processConstructors.add(new Constructor(constructorType.WAIT,processTemp2[j].replaceAll(" ", "")));
                	else if(processTemp2[j].contains("??")&&!processTemp2[j].contains("INTERRUPT("))
                		processConstructors.add(new Constructor(constructorType.CHRE,processTemp2[j].replaceAll(" ", "")));
                	else if(processTemp2[j].contains("!!")&&!processTemp2[j].contains("INTERRUPT("))
                		processConstructors.add(new Constructor(constructorType.CHSE,processTemp2[j].replaceAll(" ", "")));
                	else if(processTemp2[j].contains("if")&&processTemp2[j].contains("then"))
                		processConstructors.add(new Constructor(constructorType.COND,processTemp2[j]));
                	else if(processTemp2[j].contains("^"))
                		processConstructors.add(new Constructor(constructorType.UNDE,processTemp2[j].replaceAll(" ", "")));
                	else if(processTemp2[j].contains("**"))
                		processConstructors.add(new Constructor(constructorType.STAR,processTemp2[j].replaceAll(" ", "")));
                	else if(processTemp2[j].contains("DOT(")&&!processTemp2[j].contains("INTERRUPT(")&&!processTemp2[j].contains("@delay"))
                		processConstructors.add(new Constructor(constructorType.ODE,processTemp2[j]));
                	else if(processTemp2[j].contains("DOT(")&&processTemp2[j].contains("INTERRUPT(")&&!processTemp2[j].contains("@delay"))
                		processConstructors.add(new Constructor(constructorType.ODE_INT,processTemp2[j]));
                	else if(processTemp2[j].contains("DOT(")&&!processTemp2[j].contains("INTERRUPT(")&&processTemp2[j].contains("@delay"))
                		processConstructors.add(new Constructor(constructorType.DDE,processTemp2[j]));
                	else if(processTemp2[j].contains("DOT(")&&processTemp2[j].contains("INTERRUPT(")&&processTemp2[j].contains("@delay"))
                		processConstructors.add(new Constructor(constructorType.DDE_INT,processTemp2[j]));
                	else 
                		processConstructors.add(new Constructor(constructorType.PROC,processTemp2[j].replaceAll(" ", "")));
                }
				processes.add(processConstructors);//add every process into the list of processes
				
			    /*for(int j=0;j<processConstructors.size();j++)//test
				{
					System.out.println(processConstructors.get(j).Type);
					System.out.println(processConstructors.get(j).Content);
				}*/
			}
		}
/*		for(int i=0;i<processes.size();i++)//test
		{
			System.out.println(processes.get(i).size());
			for(int j=0;j<processes.get(i).size();j++)
			{
				System.out.println(processes.get(i).get(j).Type);
				System.out.println(processes.get(i).get(j).Content);
			}
		}*/
		return processes;
	}
	
	public static ArrayList<ODE> getODEs()//get all ODEs
	{
		ArrayList<ODE> ODEList=new ArrayList<ODE>();
		for (int i=0; i<processes.size();i++)
		{
			for(int j=0; j<processes.get(i).size();j++)//for all constructors in processes list
			{
				if (processes.get(i).get(j).Type.equals(constructorType.ODE)||processes.get(i).get(j).Type.equals(constructorType.ODE_INT))//for the two constructors contains ODE
				{
					int index=processes.get(i).get(j).Content.indexOf("DOMAIN(");
					String odeString=processes.get(i).get(j).Content.substring(0, index).replaceAll(" ", "");//get the odeString
					ODE ode=new ODE(odeString);
					ODEList.add(ode);//add into the ODEList
				}
			}
		}
/*		for(int i=0;i<ODEList.size();i++)//test
		{
			System.out.println(ODEList.get(i).odeString);
		}*/
		return ODEList;
	}
	
	public static ArrayList<DDE> getDDEs()//get all DDEs
	{
		ArrayList<DDE> DDEList=new ArrayList<DDE>();
		for (int i=0; i<processes.size();i++)
		{
			for(int j=0; j<processes.get(i).size();j++)//for all constructors in processes list
			{
				if (processes.get(i).get(j).Type.equals(constructorType.DDE)||processes.get(i).get(j).Type.equals(constructorType.DDE_INT))//for the two constructors contains DDE
				{
					int index=processes.get(i).get(j).Content.indexOf("DOMAIN(");
					String ddeString=processes.get(i).get(j).Content.substring(0, index).replaceAll(" ", "");//get the ddeString
					DDE dde=new DDE(ddeString);
					DDEList.add(dde);//add into the ODEList
				}
			}
		}
/*		for(int i=0;i<ODEList.size();i++)//test
		{
			System.out.println(ODEList.get(i).odeString);
		}*/
		return DDEList;
	}
}
