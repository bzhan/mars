package hcsp2sc;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import hcsp2sc.Constructor.constructorType;
import hcsp2sc.HCSPprocess;

public class HCSP2SystemC {
	public static String HCSPLoc="";
	public static float delta;
	public static float epsilon;
	public static float h;
	public static float varepsilon;
	public static float boundTime;
	
	public static int odeCount = 0;
	public static int dde_num;
	public static int ddename_num=1;

	public static void main(String[] args) {
		for(int i=0;i<args.length-1;i++)
		{
			if(args[i].replaceAll(" ", "").equalsIgnoreCase("-hcsploc"))
				HCSPLoc=args[i+1];
			else if (args[i].replaceAll(" ", "").equalsIgnoreCase("-delta"))
				delta=Float.parseFloat(args[i+1]);
			else if (args[i].replaceAll(" ", "").equalsIgnoreCase("-ep"))
				epsilon=Float.parseFloat(args[i+1]);
			else if (args[i].replaceAll(" ", "").equalsIgnoreCase("-h"))
				h=Float.parseFloat(args[i+1]);
			else if (args[i].replaceAll(" ", "").equalsIgnoreCase("-vep"))
				varepsilon=Float.parseFloat(args[i+1]);
			else if (args[i].replaceAll(" ", "").equalsIgnoreCase("-T"))
				boundTime=Float.parseFloat(args[i+1]);
		}
		//test
		//System.out.println("hcsplocation "+HCSPLoc+"\n"+"delta "+delta+"\n"+"epsilon "+epsilon+"\n"+"h "+h+"\n"+"varepsilon "+varepsilon+"\n");
		mainProcess();
	}
	
	public static void mainProcess()     //mainProcess
	{
		if(HCSPLoc.isEmpty())
		{
			System.out.println("file location is empty or wrong command format used, command line should be:");
			System.out.println("-hcsploc filelocation -delta float -ep float -h float -vep float");
		}
		if(delta<0 | epsilon<=0 | h<=0 | varepsilon<=0)    //values of parameters
		{
			System.out.println("All parameters should greater than 0 or wrong command format used, command line should be:");
			System.out.println("-hcsploc filelocation -delta float -ep float -h float -vep float");
			return;
		}	
		else if(varepsilon > epsilon)
		{
			System.out.println("epsilon should not less than varepsilon");
			return;
		}
		else if((h <= delta/2 || h >= delta) && delta>0)
		{
			System.out.println("h should not less than delta/2 or greater than delta");
			return;
		}
		
		if(!isRobustlySafe())   // RobustlySafe condition
		{
			System.out.println("the hcsp system in "+HCSPLoc+" is not RobustlySafe, please choose new values for -delta and -ep");
			return;
		}
		
		HCSPprocess Hprocess=new HCSPprocess();
		Hprocess.processes=Hprocess.getProcess(HCSPLoc);//get the processes list form the file
		ArrayList<ODE> ODElist=new ArrayList<ODE>();
		ArrayList<DDE> DDElist=new ArrayList<DDE>();
		ODElist=Hprocess.getODEs();//get all odes
		DDElist=Hprocess.getDDEs();//get all odes
		dde_num=DDElist.size();
		Iterator odes=ODElist.iterator();//decide the Lipschitz condition and the GAS condition
		while(odes.hasNext())
		{
			ODE ode=(ODE)odes.next();
			if(!ode.isLipschitzConstant())
			{
				System.out.println(ode.getOdeString()+" is not Lipschitz Continuous");
				return;
			}
			if(!ode.isGAS())
			{
				System.out.println(ode.getOdeString()+" is not GAS");
				return;
			}
		}
		String odeFunctions = "";
		for (int i = 0; i < ODElist.size(); i++){
			String odeString=ODElist.get(i).getOdeString();
			String varsString=odeString.substring(odeString.indexOf("DOT(")+4, odeString.indexOf(")={"));
			String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
			String[] vars = varsString.split(",");
			String[] ds = derString.split(",");
			String derivative = "double* ode" + (i+1) + "(double arguments[]){\n"
					+ "double " + varsString + ";\n"
					+ "double *temp = new double[" + vars.length + "];\n";
			for (int j = 0; j < vars.length; j++)
			{
				derivative += vars[j] + "=" + "arguments[" + j + "];";
			}
			derivative += "\n";
			for (int j = 0; j < vars.length; j++)
			{
				derivative += "temp[" + j + "]=" + ds[j] + ";";
			}
			derivative += "\nreturn temp;\n}\n";
			odeFunctions += derivative;//wanglt
		}
		//System.out.println(Hprocess.processes.get(1).get(0).Content);
		String systemCResults=Discretization(odeFunctions, Hprocess.systemName,Hprocess.parallelProcesses,Hprocess.variablesDef,Hprocess.channelsDef,Hprocess.constantsDef,Hprocess.processes); //discrete the process
		write(systemCResults);//write the result in the file	
	}
	
	public static boolean isRobustlySafe()    // RobustlySafe condition
	{
		//wait for adding......
		return true;
	}
	
	public static String Discretization(String odeFunctions, String systemName,ArrayList<String> parallelProcesses,ArrayList<String> variablesDef,ArrayList<String> channelsDef,ArrayList<String> constantsDef,ArrayList<ArrayList<Constructor>> processes) //dis results
	{
		String results="#include\"systemc.h\"\n\n";
		String constants="";
		for (int i=0;i<constantsDef.size();i++) constants+="const double "+constantsDef.get(i)+";\n";
		String DDE_count="";//DDE_count and kki (initialized as 0) are introduced for calculating the index for multiple DDEs' update
		if(dde_num>1)
		{
			for (int i=1;i<=dde_num;i++)
			{
				DDE_count+="int kk"+String.valueOf(i)+"=0;\n";
			}
		}
		results+=constants+DDE_count+"\n"; 
		results+="SC_MODULE("+systemName+"){\n";
		results+=getVarDef(variablesDef);//variables and channels declaration
		results+=getChaDef(channelsDef);
		results+="SC_CTOR("+systemName+"){\n";
		for(int i=0;i<parallelProcesses.size();i++)
		{
			results+="SC_THREAD("+parallelProcesses.get(i)+");\n";
		}
		results+="}\n";
		for(int i=0;i<processes.size();i++)//
		{
			results+=processDis(processes.get(i));
		}
		results+=odeFunctions+"};\n";
		///////// test for finding the maximal and minimal values of all the variables
		/*String test="SC_MODULE(test) {\n"
				+ "sc_in<double> s_in;\n"
				+ "double min,max;\n"
				+ "SC_CTOR(test){\n"
				+ "SC_THREAD(update);\n"
				+ "dont_initialize();\n"
				+ "sensitive<<s_in;\n"
				+ "}\n"
				+ "void update(){\n"
				+ "min=max=s_in;\n"
				+ "while(1){\n"
				+ "wait();\n"
				+ "if (s_in>max) max=s_in;\n"
				+ "if (s_in<min) min=s_in;\n}\n}\n};\n";
		String systemInstance=systemName+" myinstance(\"myinstance\");\n";
		String testInstances="";
		String reachableSets="";
		for (int i=0;i<variablesDef.size();i++)
		{
			systemInstance+="myinstance."+variablesDef.get(i)+"(s["+i+"]);\n";
			testInstances+="test mytest"+i+"(\"mytest"+i+"\");\n"
					+"mytest"+i+".s_in(s["+i+"]);\n";
			reachableSets+="cout<<\""+variablesDef.get(i)+": [\"<<mytest"+i+".min<<\", \"<<mytest"+i+".max<<\"]\"<<endl;\n";
		}
		String scmain="int sc_main(int argc,char *argv[]){\n"
				+"sc_signal<double> s["+variablesDef.size()+"];\n"
				+systemInstance
				+testInstances
				+"sc_start(+"+boundTime+",SC_SEC);\n"
				+reachableSets
				+"return 0;\n}\n";*/
///////// test for outputting all the values of all the variables
		String test="SC_MODULE(test) {\n"
				+ "sc_in<double> s_in;\n"
				+ "double values[1000];\n"
				+ "int i=0;\n"
				+ "SC_CTOR(test){\n"
				+ "SC_THREAD(update);\n"
				+ "dont_initialize();\n"
				+ "sensitive<<s_in;\n"
				+ "}\n"
				+ "void update(){\n"
				+ "while(1){\n"
				+ "wait();\n"
				+ "values[i++]=s_in;\n"
				+ "\n}\n}\n};\n";
		String systemInstance=systemName+" myinstance(\"myinstance\");\n";
		String testInstances="";
		String reachableSets="";
		for (int i=0;i<variablesDef.size();i++)
		{
			systemInstance+="myinstance."+variablesDef.get(i)+"(s["+i+"]);\n";
			testInstances+="test mytest"+i+"(\"mytest"+i+"\");\n"
					+"mytest"+i+".s_in(s["+i+"]);\n";
			reachableSets+=
"cout<<\""+variablesDef.get(i)+": [\"<<mytest"+i+".values[j]<<\"]\"<<endl;\n";
		}
		String scmain="int sc_main(int argc,char *argv[]){\n"
				+"sc_signal<double> s["+variablesDef.size()+"];\n"
				+systemInstance
				+testInstances
				+"sc_start(+"+boundTime+",SC_SEC);\n"
				+"for(int j=0;j<1100;j++)\n"+"{\n"+reachableSets+"}\n"
				+"return 0;\n}\n";
		
		
		return results+test+scmain; 
	}
	
	public static String getVarDef(ArrayList<String> variablesDef)
	{
		String results="";
		for (int i=0;i<variablesDef.size();i++)
		{
			results+="sc_out<double> "+variablesDef.get(i)+";\n";
		}
		return results;//(Lingtai)
	}
	
	public static String getChaDef(ArrayList<String> channelsDef)
	{
		String results="";
		for (int i=0;i<channelsDef.size();i++)
		{
			String ch=channelsDef.get(i);
			results+="sc_signal<double> "+ch+";\n"
					+ "sc_signal<bool> "+ch+"_r,"+ch+"_w;\n"
							+ "sc_event "+ch+"_r_done,"+ch+"_w_done;\n";
		}
		return results+"\n";//(Lingtai)
	}
	
	public static String processDis(ArrayList<Constructor> process)
	{
		String results="void "+process.get(0).Content+"(void){\n";
		for(int j=1;j<process.size();j++)//dis the process, start from the second place(because the first place stores the process itself)
		{
			results+=constructorDis(process.get(j));
		}
		return results+"}\n";
	}
	
	public static String processCall(String processName)
	{
		return processName+"();\n";
	}
	
	public static String constructorDis(Constructor c)//dis rules for different constructors
	{
		constructorType type = c.Type;
		if (type == constructorType.PROC)//for process constructor, recall processDis function
			return processCall(c.Content);
		else if (type == constructorType.SKIP) //SKIP
			return "";
		else if (type == constructorType.ASSI) //ASSI
			return c.Content +";\n"+"wait(SC_ZERO_TIME);\n";
		else if (type == constructorType.WAIT) //WAIT
			return "wait("+c.duration()+",SC_SEC);\n";
		else if (type == constructorType.CHRE) //channel receive
		{
			String ch = c.Content.substring(0,c.Content.indexOf("??")).replaceAll(" ","");
			String x = c.Content.substring(c.Content.indexOf("??")+2).replaceAll(" ","");
			return ch+"_r=1;\n"+"wait(SC_ZERO_TIME);\n"
					+"if (!"+ch+"_w) wait("+ch+"_w.posedge_event());\n"
					+"wait("+ch+"_w_done);\n"
					+x+"="+ch+".read();\n"+"wait(SC_ZERO_TIME);\n"
					+ch+"_r_done.notify();\n"
					+ch+"_r=0;\n"+"wait(SC_ZERO_TIME);\n";
		}
		else if (type == constructorType.CHSE) //channel send
		{
			String ch = c.Content.substring(0,c.Content.indexOf("!!")).replaceAll(" ","");
			String e = c.Content.substring(c.Content.indexOf("!!")+2).replaceAll(" ","");
			return ch+"_w=1;\n"+"wait(SC_ZERO_TIME);\n"
					+"if (!"+ch+"_r) wait("+ch+"_r.posedge_event());\n"
					+ch+".write("+e+");\n"+"wait(SC_ZERO_TIME);\n"
					+ch+"_w_done.notify();\n"
					+"wait("+ch+"_r_done);\n"+ch+"_w=0;\n"+"wait(SC_ZERO_TIME);\n";			
		}
		else if (type == constructorType.COND) //condition 
		{
			//System.out.println(c.Content);
			String boolExp=c.Content.substring(c.Content.indexOf("if")+2, c.Content.indexOf("then")).replaceAll(" ","");
			String proName=c.Content.substring(c.Content.indexOf("then")+4, c.Content.indexOf("else")).replaceAll(" ","");
			return "if ("+boolExp+")\n"+"{\n"+processCall(proName)+"}\n";
		}
		else if (type == constructorType.UNDE) //non-deter
		{
			String pro1=c.Content.substring(0, c.Content.indexOf("^")).replaceAll(" ","");
			String pro2=c.Content.substring(c.Content.indexOf("^")+1).replaceAll(" ","");
			return "if (rand()%2)\n"+"{\n"+processCall(pro1)+"}\n"+" else\n"+"{\n"+processCall(pro2)+"}\n";
		}
		else if (type == constructorType.STAR) //star
		{
			String pro=c.Content.substring(0, c.Content.indexOf("**")).replaceAll(" ","");			
			return "while (true)\n"+"{\n"+processCall(pro)+"}\n";
		}
/*		else if (type == constructorType.ODE){ //ODE unbounded time
			String odeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");
			String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.lastIndexOf(")")).replaceAll(" ","");
			String varsString=odeString.substring(odeString.indexOf("DOT(")+4, odeString.indexOf(")={"));
			String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
			ODE ode=new ODE(odeString);
			ode.comEpoint();
			float Epoint=ode.getEpoint();
			ode.comEtime();;
			float Etime=ode.getEtime();
			
			String[] vars = varsString.split(",");
			String[] ds = derString.split(",");
			String update = "";
			String equil = "";
			for (int i=0;i<vars.length;i++)
			{
				update += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+String.valueOf(h)+";\n";
				equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
			}
			update+="wait("+String.valueOf(h)+",SC_SEC);\n";
			equil+="wait(SC_ZERO_TIME);\n"+"return;\n";
			return "for (int i=0;i<"+String.valueOf(Math.floor(boundTime/h))+";i++)\n"+"{\n"
					+"if ("+neighborhood(boolExp,varepsilon)+")\n"+"{\n"+update+"}\n"+"else \n"+"break;\n"+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+")\n"+"{\n"+equil+"}\n";
		}*/
		
		
		
		/*else if (type == constructorType.ODE_INT){ //unbounded time
		String odeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");
		String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.indexOf(") INTERRUPT(")).replaceAll(" ","");
		String varsString=odeString.substring(odeString.indexOf("DOT(")+4, odeString.indexOf(")={"));
		String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
		ODE ode=new ODE(odeString);
		ode.comEpoint();
		float Epoint=ode.getEpoint();
		ode.comEtime();;
		float Etime=ode.getEtime();
		
		String[] vars = varsString.split(",");
		String[] ds = derString.split(",");
		
		String ss = c.Content.substring(c.Content.indexOf("INTERRUPT(")+10,c.Content.lastIndexOf(")")).replaceAll(" ","");;
		String[] events = ss.substring(ss.indexOf("{")+1,ss.indexOf("}")).split(",");
		String[] proces = ss.substring(ss.lastIndexOf("{")+1, ss.lastIndexOf("}")).split(",");
		int size = events.length;
		String[] channels = new String[size];
		String cond1 = "";
		String cond2 = "";
		String on = "";
		String off = "";
		String wait_events = "";
		String cases = "";                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   
		for (int i = 0;i < size;i++){
			if (events[i].indexOf("??")!=-1){
				channels[i] = events[i].substring(0, events[i].indexOf("??"));
				cond1 += channels[i]+"_r && !"+channels[i]+"_w"+(i<size-1?" && ":"");
				cond2 += channels[i]+"_r && "+channels[i]+"_w"+(i<size-1?" || ":"");
				on += channels[i]+"_r=1;\n";
				off += channels[i]+"_r=0;\n";
				wait_events += channels[i]+"_r.posedge_event()"+(i<size-1?"|":"");				}
			else {
				channels[i] = events[i].substring(0, events[i].indexOf("!!"));
				cond1 += channels[i]+"_w && !"+channels[i]+"_r"+(i<size-1?" && ":"");
				cond2 += channels[i]+"_w && "+channels[i]+"_r"+(i<size-1?" || ":"");
				on += channels[i]+"_w=1;\n";
				off += channels[i]+"_w=0;\n";
				wait_events += channels[i]+"_w.posedge_event()"+(i<size-1?"|":"");
			}
		}
		on += "wait(SC_ZERO_TIME);\n";
		off += "wait(SC_ZERO_TIME);\n";

		String update = "";
		String equil = "";
		for (int i=0;i<vars.length;i++)
		{
			update += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+String.valueOf(h)+";\n";
			equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
		}
		update+="wait("+String.valueOf(h)+",SC_SEC);wait(0,SC_SEC,"+wait_events+");\n";
		equil+="wait(SC_ZERO_TIME);\n"+"return;\n";
		
		for (int i = 0;i < size;i++){
			if (events[i].indexOf("??")!=-1){
				cases += "case "+i+":\n"
						+"wait("+channels[i]+"_w_done);\n"
						+events[i].substring(events[i].indexOf("??")+2)+"="+channels[i]+".read();\n"+"wait(SC_ZERO_TIME);\n"
						+channels[i]+"_r_done.notify();\n"
						+off
						+processCall(proces[i])
						+"break;\n";
			}
			else {
				cases += "case "+i+":\n"
						+channels[i]+".write("+events[i].substring(events[i].indexOf("!!")+2)+");\n"+"wait(SC_ZERO_TIME);\n"
						+channels[i]+"_w_done.notify();\n"
						+"wait("+channels[i]+"_r_done);\n"+channels[i]+"_w=0;\n"+"wait(SC_ZERO_TIME);\n"
						+off
						+processCall(proces[i])
						+"break;\n";
			}
		}
		String choose = "if ("+channels[0]+"_w&&"+channels[0]+"_r) {a[0]=1;count++;}\n";
		for (int i=1;i<size;i++){
			choose += "else if ("+channels[i]+"_w&&"+channels[i]+"_r) {a["+i+"]=1;count++;}\n";
		} 
		return on+"\n"
				+"for (int i=0;i<"+String.valueOf(Math.floor(boundTime/h))+";i++)\n"+"{\n"+"if ("+neighborhood(boolExp,varepsilon)+"&&"+cond1+")\n"+"{"+update+"}\n"+"else \n"+"break;\n"+"}\n"
		        +"if (!"+neighborhood(boolExp,varepsilon)+"&&"+cond1+")\n"+"{"+off+"}\n"
				+"if ("+cond2+"){\n"
						+ "int count=0,a["+size+"],j=-1;\n"
						+ choose
						+"int k=rand()%count;\n"
						+ "while(k>=0){j++;if(a[j])k--;}\n"
						+ "switch(j){\n"+cases+"}\n"
				+"}\n"
				+"if ("+neighborhood(boolExp,varepsilon)+"&& "+cond1+"){\n"+equil+"}\n";
	}
*/

		
	/*	else if (type == constructorType.ODE){ //ODE bounded time - Euler method 
			String odeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");
			String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.lastIndexOf(")")).replaceAll(" ","");
			String varsString=odeString.substring(odeString.indexOf("DOT(")+4, odeString.indexOf(")={"));
			String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
			ODE ode=new ODE(odeString);
			ode.comEpoint();
			float Epoint=ode.getEpoint();
			ode.comEtime();;
			float Etime=ode.getEtime();
			
			String[] vars = varsString.split(",");
			String[] ds = derString.split(",");
			String update = "";
			String update_prime = "";
			String boolExp_prime = "";
			String equil = "";
			String h_prime="";
			if(boundTime-Math.floor(boundTime/h)*h<1E-9)
				h_prime=String.valueOf(0);
			else
			    h_prime=String.valueOf(boundTime-Math.floor(boundTime/h)*h);
			update+="wait("+String.valueOf(h)+",SC_SEC);\n";
			update_prime+="wait("+h_prime+",SC_SEC);\n";
			for (int i=0;i<vars.length;i++)
			{
				update += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+String.valueOf(h)+";\n";
				update_prime += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+h_prime+";\n";
				boolExp_prime=boolExp.replaceAll(vars[i], vars[i]+"+("+ds[i]+")*"+String.valueOf(h));
				//equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
			}
			update+="wait(SC_ZERO_TIME);\n";
			update_prime+="wait(SC_ZERO_TIME);\n";
			equil+="return;\n";
			return "for (int i=0;i<"+String.valueOf(Math.floor(boundTime/h))+";i++)\n"+"{\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+update+"}\n"+"else \n"+"break;\n"+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+update_prime+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+equil+"}\n";
		}
		*/



		/*else if (type == constructorType.ODE_INT){ //bounded time - Euler method 
			String odeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");
			String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.indexOf(") INTERRUPT(")).replaceAll(" ","");
			String varsString=odeString.substring(odeString.indexOf("DOT(")+4, odeString.indexOf(")={"));
			String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
			ODE ode=new ODE(odeString);
			ode.comEpoint();
			float Epoint=ode.getEpoint();
			ode.comEtime();;
			float Etime=ode.getEtime();
			
			String[] vars = varsString.split(",");
			String[] ds = derString.split(",");
			
			String ss = c.Content.substring(c.Content.indexOf("INTERRUPT(")+10,c.Content.lastIndexOf(")")).replaceAll(" ","");;
			String[] events = ss.substring(ss.indexOf("{")+1,ss.indexOf("}")).split(",");
			String[] proces = ss.substring(ss.lastIndexOf("{")+1, ss.lastIndexOf("}")).split(",");
			int size = events.length;
			String[] channels = new String[size];
			String cond1 = "";
			String cond2 = "";
			String on = "";
			String off = "";
			String wait_events = "";
			String cases = "";                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   
			for (int i = 0;i < size;i++){
				if (events[i].indexOf("??")!=-1){
					channels[i] = events[i].substring(0, events[i].indexOf("??"));
					cond1 += channels[i]+"_r && !"+channels[i]+"_w"+(i<size-1?" && ":"");
					cond2 += channels[i]+"_r && "+channels[i]+"_w"+(i<size-1?" || ":"");
					on += channels[i]+"_r=1;\n";
					off += channels[i]+"_r=0;\n";
					wait_events += channels[i]+"_r.posedge_event()"+(i<size-1?"|":"");				}
				else {
					channels[i] = events[i].substring(0, events[i].indexOf("!!"));
					cond1 += channels[i]+"_w && !"+channels[i]+"_r"+(i<size-1?" && ":"");
					cond2 += channels[i]+"_w && "+channels[i]+"_r"+(i<size-1?" || ":"");
					on += channels[i]+"_w=1;\n";
					off += channels[i]+"_w=0;\n";
					wait_events += channels[i]+"_w.posedge_event()"+(i<size-1?"|":"");
				}
			}
			on += "wait(SC_ZERO_TIME);\n";
			off += "wait(SC_ZERO_TIME);\n";
		
			String update = "";
			String update_prime = "";
			String boolExp_prime = "";
			String equil = "";
			String h_prime="";
			if(boundTime-Math.floor(boundTime/h)*h<1E-9)
				h_prime=String.valueOf(0);
			else
			    h_prime=String.valueOf(boundTime-Math.floor(boundTime/h)*h);
			update+="wait("+String.valueOf(h)+",SC_SEC);\n";
			update_prime+="wait("+h_prime+",SC_SEC);\n";
			for (int i=0;i<vars.length;i++)
			{
				update += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+String.valueOf(h)+";\n";
				update_prime += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+h_prime+";\n";
				boolExp_prime=boolExp.replaceAll(vars[i], vars[i]+"+("+ds[i]+")*"+String.valueOf(h));
				//equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
			}
			update+="wait(0,SC_SEC,"+wait_events+");\n";
			update_prime+="wait(SC_ZERO_TIME);\n";
			equil+="return;\n";
			
			for (int i = 0;i < size;i++){
				if (events[i].indexOf("??")!=-1){
					cases += "case "+i+":\n"
							+"wait("+channels[i]+"_w_done);\n"
							+events[i].substring(events[i].indexOf("??")+2)+"="+channels[i]+".read();\n"+"wait(SC_ZERO_TIME);\n"
							+channels[i]+"_r_done.notify();\n"
							+off
							+processCall(proces[i])
							+"break;\n";
				}
				else {
					cases += "case "+i+":\n"
							+channels[i]+".write("+events[i].substring(events[i].indexOf("!!")+2)+");\n"+"wait(SC_ZERO_TIME);\n"
							+channels[i]+"_w_done.notify();\n"
							+"wait("+channels[i]+"_r_done);\n"+channels[i]+"_w=0;\n"+"wait(SC_ZERO_TIME);\n"
							+off
							+processCall(proces[i])
							+"break;\n";
				}
			}
			String choose = "if ("+channels[0]+"_w&&"+channels[0]+"_r) {a[0]=1;count++;}\n";
			for (int i=1;i<size;i++){
				choose += "else if ("+channels[i]+"_w&&"+channels[i]+"_r) {a["+i+"]=1;count++;}\n";
			} 
			return on+"\n"
					+"for (int i=0;i<"+String.valueOf(Math.floor(boundTime/h))+";i++)\n"+"{\n"+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&&"+cond1+")\n"+"{"+update+"}\n"+"else \n"+"break;\n"+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&&"+cond1+")\n"+"{"+update_prime+"}\n"
			        +"if (!("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")&&"+cond1+")\n"+"{"+off+"}\n"
					+"if ("+cond2+"){\n"
							+ "int count=0,a["+size+"],j=-1;\n"
							+ choose
							+"int k=rand()%count;\n"
							+ "while(k>=0){j++;if(a[j])k--;}\n"
							+ "switch(j){\n"+cases+"}\n"
					+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&& "+cond1+"){\n"+equil+"}\n";
		}
*/
		else if (type == constructorType.DDE){ //DDE bounded time - Euler method
			
			String final_string="";
			String ddeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");//dde string
			String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.lastIndexOf(")")).replaceAll(" ","");//bool condition string
			String varsString=ddeString.substring(ddeString.indexOf("DOT(")+4, ddeString.indexOf(")={"));//variables string
			//String derString=ddeString.substring(ddeString.indexOf("={")+2, ddeString.lastIndexOf("}"));
			DDE dde=new DDE(ddeString);// new a dde
			String tempDir=HCSPLoc.substring(0, HCSPLoc.lastIndexOf("/"));
			dde.setSimResultAddr(tempDir+"/simResult.txt");//set its address of the simulation result file
			int shift_index=2;//one DDE with shift_index=2, and more than one DDE with shift_index=0
			String kk_update=""; //kki++, for reading the next element in the array var_dde_values
			if(dde_num>1) // more than one dde
			{
				dde.setDdeName("DDE"+String.valueOf(ddename_num)); //set the name of DDEs
				kk_update="kk"+String.valueOf(ddename_num)+"++;\n"; // update the kk_update
				ddename_num++;
				shift_index=0; // dde_num means more than one dde, so the shift_update is assigned to 0
			}
			ArrayList<String> values=dde.getValues();//read the simulation result from the file
			//System.out.println(values.get(1));
			String[] vars = varsString.split(",");//store the variables' name in an array 
			for(int i=0;i<vars.length;i++)
			{
				if(vars.length==1)// for one variable
				{
					final_string+="double "+vars[i]+"_"+dde.getDdeName()+"_values["+String.valueOf(values.size()-shift_index)+"]={";//new an array for storing its values that reading from the file (the first two for time<0 and time=0 are omitted)
					for(int j=shift_index;j<values.size();j++)// as the first two elements are omitted, j starts from 2
					{
						if(j==values.size()-1)//the last one
							final_string+=values.get(j)+"};\n";//add into the new array
						else// not the last one
						    final_string+=values.get(j)+",";
					}
				}
				else //more than one variable
				{
					final_string+="double "+vars[i]+"_"+dde.getDdeName()+"_values["+String.valueOf(values.size()-shift_index)+"]={";
					for(int j=shift_index;j<values.size();j++)
					{
						//System.out.println(values.get(j));
						String[] temp=values.get(j).split(",");//split the vars.length variable
						if(j==values.size()-1)
							final_string+=temp[i]+"};\n";// add the i-th element of temp to the i-th array
						else
						    final_string+=temp[i]+",";// add the i-th element of temp to the i-th array
					}
				}			
			}
			//String[] ds = derString.split(",");

			String update = ""; // string for variables' update
			//String update_prime = "";
			String boolExp_prime = ""; // string for N_prime
			String equil = "";
			//String h_prime="";
			/*if(boundTime-Math.floor(boundTime/h)*h<1E-9)
				h_prime=String.valueOf(0);
			else
			    h_prime=String.valueOf(boundTime-Math.floor(boundTime/h)*h);*/
			update+="wait("+String.valueOf(h)+",SC_SEC);\n"; //wait statement
/*			update += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
*//*			update_prime+="wait("+h_prime+",SC_SEC);\n";
			update_prime += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h_prime +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h_prime +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h_prime +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
*/			for (int i=0;i<vars.length;i++) // the update of the assignment and the bool expression
			{
                update += vars[i]+"="+vars[i]+"_"+dde.getDdeName()+"_values["+kk_update.substring(0, kk_update.indexOf("++"))+"]"+";\n"+kk_update;// variables update according to the new arrays which read the simulation result from the simResult.txt
				//update_prime += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+h_prime+";\n";
				boolExp_prime=boolExp.replaceAll(vars[i], vars[i]+"_"+dde.getDdeName()+"_values["+kk_update.substring(0, kk_update.indexOf("++"))+"]");
				//equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
			}
			update+="wait(SC_ZERO_TIME);\n";
			//update_prime+="wait(SC_ZERO_TIME);\n";
			equil+="return;\n";
			final_string+="for (int i=0;i<"+String.valueOf(Math.ceil(boundTime/h))+";i++)\n"+"{\n" // a for statement in the SystemC for update 
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+update+"}\n"+"else \n"+"break;\n"+"}\n"
					
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+equil+"}\n";
			return final_string;
		}
		
		else if (type == constructorType.DDE_INT){ //DDE_INT bounded time - Euler method			
			String final_string="";
			String ddeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");
			String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.indexOf(") INTERRUPT(")).replaceAll(" ","");
			String varsString=ddeString.substring(ddeString.indexOf("DOT(")+4, ddeString.indexOf(")={"));
			//String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
			DDE dde=new DDE(ddeString);
			String tempDir=HCSPLoc.substring(0, HCSPLoc.lastIndexOf("/"));
			dde.setSimResultAddr(tempDir+"/simResult.txt");
			int shift_index=2;//one DDE for 2, and 0 for more than one DDE
			String kk_update="";
			if(dde_num>1)
			{
				dde.setDdeName("DDE"+String.valueOf(ddename_num));
				kk_update="kk"+String.valueOf(ddename_num)+"++;\n";
				ddename_num++;
				shift_index=0;
			}
			ArrayList<String> values=dde.getValues();//read the simulation result from the file
			//System.out.println(values.get(2));
			
			String[] vars = varsString.split(",");
			for(int i=0;i<vars.length;i++)
			{
				if(vars.length==1)// for one variable
				{
					
					final_string+="double "+vars[i]+"_"+dde.getDdeName()+"_values["+String.valueOf(values.size()-shift_index)+"]={";//new an array for storing its values that reading from the file (the first two for time<0 and time=0 are omitted)
					for(int j=shift_index;j<values.size();j++)// as the first two elements are omitted, j starts from 2
					{
						if(j==values.size()-1)//the last one
							final_string+=values.get(j)+"};\n";//add into the new array
						else// not the last one
						    final_string+=values.get(j)+",";
					}
					
				}
				else //more than one variable
				{
					final_string+="double "+vars[i]+"_"+dde.getDdeName()+"_values["+String.valueOf(values.size()-shift_index)+"]={";
					for(int j=shift_index;j<values.size();j++)
					{
						//System.out.println(values.get(j));
						String[] temp=values.get(j).split(",");//split the vars.length variable
						if(j==values.size()-1)
							final_string+=temp[i]+"};\n";// add the i-th element of temp to the i-th array
						else
						    final_string+=temp[i]+",";// add the i-th element of temp to the i-th array
					}
				}			
			}
			//System.out.println(final_string);
			//String[] ds = derString.split(",");
			
			String ss = c.Content.substring(c.Content.indexOf("INTERRUPT(")+10,c.Content.lastIndexOf(")")).replaceAll(" ","");;
			String[] events = ss.substring(ss.indexOf("{")+1,ss.indexOf("}")).split(",");// all events
			String[] process = ss.substring(ss.lastIndexOf("{")+1, ss.lastIndexOf("}")).split(",");// all processes followed
			int size = events.length;
			String[] channels = new String[size];
			String cond1 = "";
			String cond2 = "";
			String on = "";
			String off = "";
			String wait_events = "";
			String cases = "";                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   
			for (int i = 0;i < size;i++){
				if (events[i].indexOf("??")!=-1){
					channels[i] = events[i].substring(0, events[i].indexOf("??"));
					cond1 += channels[i]+"_r && !"+channels[i]+"_w"+(i<size-1?" && ":"");
					cond2 += channels[i]+"_r && "+channels[i]+"_w"+(i<size-1?" || ":"");
					on += channels[i]+"_r=1;\n";
					off += channels[i]+"_r=0;\n";
					wait_events += channels[i]+"_r.posedge_event()"+(i<size-1?"|":"");				}
				else {
					channels[i] = events[i].substring(0, events[i].indexOf("!!"));
					cond1 += channels[i]+"_w && !"+channels[i]+"_r"+(i<size-1?" && ":"");
					cond2 += channels[i]+"_w && "+channels[i]+"_r"+(i<size-1?" || ":"");
					on += channels[i]+"_w=1;\n";
					off += channels[i]+"_w=0;\n";
					wait_events += channels[i]+"_w.posedge_event()"+(i<size-1?"|":"");
				}
			}
			on += "wait(SC_ZERO_TIME);\n";
			off += "wait(SC_ZERO_TIME);\n";
		
			String update = "";
			//String update_prime = "";
			String boolExp_prime = "";
			String equil = "";
			//String h_prime="";
			/*if(boundTime-Math.floor(boundTime/h)*h<1E-9)
				h_prime=String.valueOf(0);
			else
			    h_prime=String.valueOf(boundTime-Math.floor(boundTime/h)*h);*/
			update+="wait("+String.valueOf(h)+",SC_SEC);\n";
/*			update += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
			update_prime+="wait("+h_prime+",SC_SEC);\n";
			update_prime += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h_prime +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h_prime +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h_prime +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
*/			for (int i=0;i<vars.length;i++)
			{
//				update += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+String.valueOf(h)+";\n";
//				update_prime += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+h_prime+";\n";
	            update += vars[i]+"="+vars[i]+"_"+dde.getDdeName()+"_values["+kk_update.substring(0, kk_update.indexOf("++"))+"]"+";\n"+kk_update;// variables update according to the new arrays which read the simulation result from the simResult.txt
				boolExp_prime=boolExp.replaceAll(vars[i], vars[i]+"_"+dde.getDdeName()+"_values["+kk_update.substring(0, kk_update.indexOf("++"))+"]");// In fact, need be a value
				//equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
			}
			update+="wait(0,SC_SEC,"+wait_events+");\n";
			//update_prime+="wait(SC_ZERO_TIME);\n";
			equil+="return;\n";
			
			for (int i = 0;i < size;i++){
				if (events[i].indexOf("??")!=-1){
					cases += "case "+i+":\n"
							+"wait("+channels[i]+"_w_done);\n"
							+events[i].substring(events[i].indexOf("??")+2)+"="+channels[i]+".read();\n"+"wait(SC_ZERO_TIME);\n"
							+channels[i]+"_r_done.notify();\n"
							+off
							+processCall(process[i])
							+"break;\n";
				}
				else {
					cases += "case "+i+":\n"
							+channels[i]+".write("+events[i].substring(events[i].indexOf("!!")+2)+");\n"+"wait(SC_ZERO_TIME);\n"
							+channels[i]+"_w_done.notify();\n"
							+"wait("+channels[i]+"_r_done);\n"+channels[i]+"_w=0;\n"+"wait(SC_ZERO_TIME);\n"
							+off
							+processCall(process[i])
							+"break;\n";
				}
			}
			String choose = "if ("+channels[0]+"_w&&"+channels[0]+"_r) {a[0]=1;count++;}\n";
			for (int i=1;i<size;i++){
				choose += "else if ("+channels[i]+"_w&&"+channels[i]+"_r) {a["+i+"]=1;count++;}\n";
			} 
			final_string+=on+"\n"
					+"for (int i=0;i<"+String.valueOf(Math.ceil(boundTime/h))+";i++)\n"+"{\n"+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&&"+cond1+")\n"+"{"+update+"}\n"+"else \n"+"break;\n"+"}\n"
			        +"if (!("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")&&"+cond1+")\n"+"{"+off+"}\n"
					+"if ("+cond2+"){\n"
							+ "int count=0,a["+size+"],j=-1;\n"
							+ choose
							+"int k=rand()%count;\n"
							+ "while(k>=0){j++;if(a[j])k--;}\n"
							+ "switch(j){\n"+cases+"}\n"
					+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&& "+cond1+"){\n"+equil+"}\n";
			return final_string;
		}
		
		
		else if (type == constructorType.ODE){ //ODE bounded time - Runge Kutta method
			odeCount++;
			
			String final_string="";
			String odeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");
			String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.lastIndexOf(")")).replaceAll(" ","");
			String varsString=odeString.substring(odeString.indexOf("DOT(")+4, odeString.indexOf(")={"));
			String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
			ODE ode=new ODE(odeString);
			ode.comEpoint();
			float Epoint=ode.getEpoint();
			ode.comEtime();;
			float Etime=ode.getEtime();
			
			String[] vars = varsString.split(",");
			String[] ds = derString.split(",");

			String update = "";
			String update_prime = "";
			String boolExp_prime = "";
			String equil = "";
			String h_prime="";
			if(boundTime-Math.floor(boundTime/h)*h<1E-9)
				h_prime=String.valueOf(0);
			else
			    h_prime=String.valueOf(boundTime-Math.floor(boundTime/h)*h);
			update+="wait("+String.valueOf(h)+",SC_SEC);\n";
			update += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
			update_prime+="wait("+h_prime+",SC_SEC);\n";
			update_prime += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h_prime +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h_prime +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h_prime +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
			for (int i=0;i<vars.length;i++)
			{
				//update += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+String.valueOf(h)+";\n";
				//update_prime += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+h_prime+";\n";
				update += vars[i]+"="+vars[i]+"+phi["+i+"]*"+String.valueOf(h)+";\n";//wanglt
				update_prime += vars[i]+"="+vars[i]+"+phi["+i+"]*"+h_prime+";\n";//wanglt
				boolExp_prime=boolExp.replaceAll(vars[i], vars[i]+"+("+ds[i]+")*"+String.valueOf(h));
				//equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
			}
			update+="wait(SC_ZERO_TIME);\n";
			update_prime+="wait(SC_ZERO_TIME);\n";
			equil+="return;\n";
			final_string="for (int i=0;i<"+String.valueOf(Math.floor(boundTime/h))+";i++)\n"+"{\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+update+"}\n"+"else \n"+"break;\n"+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+update_prime+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")\n"+"{\n"+equil+"}\n";
			return final_string;
		}
				
	
		
		else if (type == constructorType.ODE_INT){ //ODE_INT bounded time - Runge Kutta method
			odeCount++;
			
			String final_string="";
			String odeString=c.Content.substring(0, c.Content.indexOf("DOMAIN(")).replaceAll(" ","");
			String boolExp=c.Content.substring(c.Content.indexOf("DOMAIN(")+7,c.Content.indexOf(") INTERRUPT(")).replaceAll(" ","");
			String varsString=odeString.substring(odeString.indexOf("DOT(")+4, odeString.indexOf(")={"));
			String derString=odeString.substring(odeString.indexOf("={")+2, odeString.lastIndexOf("}"));
			ODE ode=new ODE(odeString);
			ode.comEpoint();
			float Epoint=ode.getEpoint();
			ode.comEtime();;
			float Etime=ode.getEtime();
			
			String[] vars = varsString.split(",");
			String[] ds = derString.split(",");
			
			String ss = c.Content.substring(c.Content.indexOf("INTERRUPT(")+10,c.Content.lastIndexOf(")")).replaceAll(" ","");;
			String[] events = ss.substring(ss.indexOf("{")+1,ss.indexOf("}")).split(",");
			String[] proces = ss.substring(ss.lastIndexOf("{")+1, ss.lastIndexOf("}")).split(",");
			int size = events.length;
			String[] channels = new String[size];
			String cond1 = "";
			String cond2 = "";
			String on = "";
			String off = "";
			String wait_events = "";
			String cases = "";                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   
			for (int i = 0;i < size;i++){
				if (events[i].indexOf("??")!=-1){
					channels[i] = events[i].substring(0, events[i].indexOf("??"));
					cond1 += channels[i]+"_r && !"+channels[i]+"_w"+(i<size-1?" && ":"");
					cond2 += channels[i]+"_r && "+channels[i]+"_w"+(i<size-1?" || ":"");
					on += channels[i]+"_r=1;\n";
					off += channels[i]+"_r=0;\n";
					wait_events += channels[i]+"_r.posedge_event()"+(i<size-1?"|":"");				}
				else {
					channels[i] = events[i].substring(0, events[i].indexOf("!!"));
					cond1 += channels[i]+"_w && !"+channels[i]+"_r"+(i<size-1?" && ":"");
					cond2 += channels[i]+"_w && "+channels[i]+"_r"+(i<size-1?" || ":"");
					on += channels[i]+"_w=1;\n";
					off += channels[i]+"_w=0;\n";
					wait_events += channels[i]+"_w.posedge_event()"+(i<size-1?"|":"");
				}
			}
			on += "wait(SC_ZERO_TIME);\n";
			off += "wait(SC_ZERO_TIME);\n";
		
			String update = "";
			String update_prime = "";
			String boolExp_prime = "";
			String equil = "";
			String h_prime="";
			if(boundTime-Math.floor(boundTime/h)*h<1E-9)
				h_prime=String.valueOf(0);
			else
			    h_prime=String.valueOf(boundTime-Math.floor(boundTime/h)*h);
			update+="wait("+String.valueOf(h)+",SC_SEC);\n";
			update += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
			update_prime+="wait("+h_prime+",SC_SEC);\n";
			update_prime += "double currentX[" + vars.length + "] = {" + varsString + "};\n"
					+ "double arguments[" + vars.length + "];\n"
					+ "double phi[" + vars.length + "];\n"
					+ "double *k1 = ode" + odeCount + "(currentX);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k1[j] / 2 * " + h_prime +";\n"
							+ "phi[j] = k1[j] / 6;\n"
					+ "}\n"
					+ "double *k2 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k2[j] / 2 * " + h_prime +";\n"
							+ "phi[j] += k2[j] / 3;\n"
					+ "}\n"
					+ "double *k3 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "arguments[j] = currentX[j] + k3[j] * " + h_prime +";\n"
							+ "phi[j] += k3[j] / 3;\n"
					+ "}\n"
					+ "double *k4 = ode" + odeCount + "(arguments);\n"
					+ "for (int j=0; j<" + vars.length + "; j++){\n"
							+ "phi[j] += k4[j] / 6;\n"
					+ "}\n";//wanglt
			for (int i=0;i<vars.length;i++)
			{
//				update += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+String.valueOf(h)+";\n";
//				update_prime += vars[i]+"="+vars[i]+"+("+ds[i]+")*"+h_prime+";\n";
				update += vars[i] + "=" + vars[i] + "+phi[" + i + "]*" + String.valueOf(h) + ";\n";//wanglt
				update_prime += vars[i] + "=" + vars[i] + "+phi[" + i + "]*" + h_prime + ";\n";//wanglt
				boolExp_prime=boolExp.replaceAll(vars[i], vars[i]+"+("+ds[i]+")*"+String.valueOf(h));
				//equil += vars[i]+"="+String.valueOf(Epoint)+";\n"; 
			}
			update+="wait(0,SC_SEC,"+wait_events+");\n";
			update_prime+="wait(SC_ZERO_TIME);\n";
			equil+="return;\n";
			
			for (int i = 0;i < size;i++){
				if (events[i].indexOf("??")!=-1){
					cases += "case "+i+":\n"
							+"wait("+channels[i]+"_w_done);\n"
							+events[i].substring(events[i].indexOf("??")+2)+"="+channels[i]+".read();\n"+"wait(SC_ZERO_TIME);\n"
							+channels[i]+"_r_done.notify();\n"
							+off
							+processCall(proces[i])
							+"break;\n";
				}
				else {
					cases += "case "+i+":\n"
							+channels[i]+".write("+events[i].substring(events[i].indexOf("!!")+2)+");\n"+"wait(SC_ZERO_TIME);\n"
							+channels[i]+"_w_done.notify();\n"
							+"wait("+channels[i]+"_r_done);\n"+channels[i]+"_w=0;\n"+"wait(SC_ZERO_TIME);\n"
							+off
							+processCall(proces[i])
							+"break;\n";
				}
			}
			String choose = "if ("+channels[0]+"_w&&"+channels[0]+"_r) {a[0]=1;count++;}\n";
			for (int i=1;i<size;i++){
				choose += "else if ("+channels[i]+"_w&&"+channels[i]+"_r) {a["+i+"]=1;count++;}\n";
			} 
			final_string=on+"\n"
					+"for (int i=0;i<"+String.valueOf(Math.floor(boundTime/h))+";i++)\n"+"{\n"+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&&"+cond1+")\n"+"{"+update+"}\n"+"else \n"+"break;\n"+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&&"+cond1+")\n"+"{"+update_prime+"}\n"
			        +"if (!("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+")&&"+cond1+")\n"+"{"+off+"}\n"
					+"if ("+cond2+"){\n"
							+ "int count=0,a["+size+"],j=-1;\n"
							+ choose
							+"int k=rand()%count;\n"
							+ "while(k>=0){j++;if(a[j])k--;}\n"
							+ "switch(j){\n"+cases+"}\n"
					+"}\n"
					+"if ("+neighborhood(boolExp,varepsilon)+"&&"+neighborhood(boolExp_prime,varepsilon)+"&& "+cond1+"){\n"+equil+"}\n";
			return final_string;
		}
		
		
		
		
		else{
			return "not finished yet";
		}
	}
	
	public static String neighborhood(String B, float epsilon)
	{
		String result="";
		if(B.equals("true")||B.equals("(true)")||B.equals("TRUE")||B.equals("(TRUE)"))
			result="true";
		else
		{
			String[] temp=B.split("&&");
			for(int i=0;i<temp.length;i++)
			{
				if(temp[i].contains(">")||temp[i].contains(">="))
				{
					temp[i]+="-"+String.valueOf(epsilon);
				}
				else if(temp[i].contains("<")||temp[i].contains("<="))
				{
					temp[i]+="+"+String.valueOf(epsilon);
				}
				else if(temp[i].contains("=="))
				{
					temp[i]=temp[i].substring(temp[i].indexOf("==")+2)+"-"+String.valueOf(epsilon)+"<="+temp[i].substring(0,temp[i].indexOf("=="))+"<="+temp[i].substring(temp[i].indexOf("==")+2)+"+"+String.valueOf(epsilon);
				}
				if (i==temp.length-1)
				    result+=temp[i];
				else
					result+=temp[i]+"&&";
			}
		}
		return result;
	}
	
	public static void write(String result)
	{
		try {
			BufferedWriter output=new BufferedWriter(new FileWriter(HCSPLoc.replaceAll(".hcsp", ".cpp")));
			output.write(result);
			output.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}