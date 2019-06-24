package m2h;

import java.util.ArrayList;
import java.util.HashMap;

import model.S2M;
import model.SL_Block;
import model.SL_Diagram;
import model.SL_Line;
import model.stateflow.SFIsabelle;
import model.stateflow.SFProcess;
import model.stateflow.Stateflow;
import model.subsystems.SubSystem;

@SuppressWarnings("unused")
public class SL2HCSP {
	public static String textInit = "";
	public static String textRep = "";
	public static ArrayList<String> textCState = new ArrayList<String>();
	public static String basicClock = "";

	public static String currentLoc;
	public static String udsLocation;
	public static boolean isCompact = false;
	public static boolean open = false;
	public static boolean printText = false;
	public static boolean printSFText = false;
	public static String sample = "";
	public static boolean sfNet = true;

	// debug options
	private static boolean printCommLines = true;
	public final static boolean rewriteAll = true;
	public final static boolean rewriteAss = false;

	public static void main(String[] args) {
		String xmlLocation = "";

		for (int i = 0; i < args.length - 1; i++) {
			if (args[i].replaceAll(" ", "").equals("-compact"))
				isCompact = Boolean.valueOf(args[i + 1]);
			else if (args[i].replaceAll(" ", "").equals("-xml")) {
				xmlLocation = args[i + 1];
				currentLoc = xmlLocation.substring(0, xmlLocation.lastIndexOf("/") + 1);
			} else if (args[i].replaceAll(" ", "").equals("-uds"))
				udsLocation = args[i + 1];
			else if (args[i].replaceAll(" ", "").equals("-open"))//这四个选项是什么意思？
				open = Boolean.valueOf(args[i + 1]);
			else if (args[i].replaceAll(" ", "").equals("-print"))
				printText = Boolean.valueOf(args[i + 1]);
			else if (args[i].replaceAll(" ", "").equals("-printSF"))
				printSFText = Boolean.valueOf(args[i + 1]);
			else if (args[i].replaceAll(" ", "").equals("-sfNet"))
				sfNet = Boolean.valueOf(args[i + 1]);
		}

		mainProcess(xmlLocation);
	}

	public static void mainProcess(String xmlLocation) {

		// Load Simulink model.
		SL_Diagram diagram = loadModel(xmlLocation);
		if (diagram == null)
			return;
		// diagram.printDiagram(0);
		// diagram.printStateflow();

		ArrayList<ArrayList<String>> partition = Partition.partition(diagram);
		// partition contains continuous and discrete parts, e.g [[pant_add1,plant_product1],[control_Constant1,control_add1]]
		//System.out.print("@@@@@@@@@"+partition+"@@@@@@@@@@");
		// Partition.printPartition(partition);
		String buf = Comms.dealWithComms(diagram);

		// handle triggered subsystems
		SubSys.triggeredSubSys(diagram);

		// handle enabled subsystems
		SubSys.enableSubSys(diagram);

		// get processes
		ArrayList<String> discreteProcesses = new ArrayList<String>();
		ArrayList<HashMap<String, ArrayList<String>>> continuousProcesses = new ArrayList<HashMap<String, ArrayList<String>>>();
		if (!buf.isEmpty())
			discreteProcesses.add(buf);
		for (int i = 0; i < partition.size(); i++) {
			ArrayList<String> aPartition = partition.get(i);
			//System.out.print("@@@@@@@@@"+aPartition+"@@@@@@@@@@");
			// handle Stateflow
			if (aPartition.size() == 1//stateflow size=1
					&& diagram.getBlocks().get(aPartition.get(0)).getType()
							.equals("Stateflow")) {
				Stateflow sf = (Stateflow) diagram.getBlocks().get(
						aPartition.get(0));
				SFIsabelle.isabelle(sf);
				//Isabelle.isabelleWrite("system.hcsp", SFIsabelle.getProcesses(sf));
				continue;
			}
			if (aPartition.size() == 1//trigger subsys size=1
					&& diagram.getBlocks().get(aPartition.get(0)).getType()
							.equals("SubSystem")
					&& ((SubSystem) diagram.getBlocks().get(aPartition.get(0)))
							.getSystemType().equals("Trigger")) {
				discreteProcesses.add(((SubSystem) diagram.getBlocks().get(
						aPartition.get(0))).getProcess());
			} else if (diagram.getBlocks().get(aPartition.get(0))//continuous processes size>1
					.getParameters().get("st").equals("0")
					&& !diagram.getBlocks().get(aPartition.get(0)).getParameters().keySet().contains("discrete")) {
				HashMap<String, ArrayList<String>> process = C_Process.getProcess(diagram, aPartition);
				//System.out.println("@@@@@@@@@"+process+"@@@@@@@@@@");
				for (int j = 0; j < process.get("state").size(); j++) {
					//System.out.println("@@@@@@@@@"+process.get("state").get(j)+"@@@@@@@@@@");
					String newState = Optimization.deleteConstantVariable(
							diagram, process.get("state").get(j));
					//System.out.println("@@@@@@@@@"+newState+"@@@@@@@@@@");
					process.get("state").set(j, newState);
					
				}
				
				//System.out.println("*********@@"+continuousProcesses+"@@@@@@@@@@");
				continuousProcesses.add(process);
			} else {//discrete processes
				String aDiscreteProcess = D_Process.getProcess(diagram,
						aPartition, i);
				aDiscreteProcess = Optimization.deleteConstantVariable(diagram,
						aDiscreteProcess);
				discreteProcesses.add(aDiscreteProcess);
			}
		}
		// System.out.println("Print continuous processes:");
		for(int i = 0; i < continuousProcesses.size(); i++)
			System.out.println(i+"-----"+continuousProcesses.get(i));
        //System.out.println("@@@@@@@@@"+continuousProcesses+"@@@@@@@@@@");
		String process = C_Process.getProcesses(continuousProcesses);
		//System.out.println("*********@@"+process+"@&&&&&&&&&@@");
		process += D_Process.getProcesses(discreteProcesses);
		process = process.replaceAll("null;\n", "");
		process = process.replaceAll(";\n;", ";");
		process = process.replaceAll(";;", ";");
		if (printText)
			System.out.println(process);

		if (printText)
			Isabelle.isabelleWrite("textualProcesses", process);

		//if (discreteProcesses.isEmpty() || continuousProcesses.isEmpty()) {
		//	return;
		//}
		Isabelle.isabelle(diagram, discreteProcesses, continuousProcesses);
		SL2HCSP.textRep += "temp:=t;";
		if (SL2HCSP.textCState.isEmpty())
			SL2HCSP.textCState.add("");
		for (int i = 0; i + 1 < SL2HCSP.textCState.size(); ++i)
			SL2HCSP.textRep += SL2HCSP.textCState.get(i) + "temp + (Real "
					+ SL2HCSP.basicClock + ")>>;\n";
		SL2HCSP.textRep += SL2HCSP.textCState
				.get(SL2HCSP.textCState.size() - 1)
				+ "temp + (Real "
				+ SL2HCSP.basicClock + ")>>";
		String text = SL2HCSP.textInit + "t:=(Real 0);\n(" + SL2HCSP.textRep
				+ ")*";
		text = text.replaceAll("Real", "Real ");
		// System.out.println(text);
		Isabelle.isabelleWrite("process", text);
	}

	public static SL_Diagram loadModel(String xmlLocation) {//从xml得到Simulink-diagram
		SL_Diagram diagram = S2M.s2m(xmlLocation);
		if (diagram.isBroken()) {
			System.out.println("The diagram is broken!");
			return null;
		}

		SubSys.deleteNomalSubSys(diagram);
		Optimization.deleteUselessBlocks(diagram);

		if (!SampleTime.calSampleTime(diagram)) {
			return null;
		}

		// check if name are not valid
		if (!nameCheck(diagram)) {
			return null;
		}

		return diagram;
	}

	public static boolean nameCheck(SL_Diagram diagram) {
		for (SL_Block b1 : diagram.getBlocks().values()) {
			for (SL_Block b2 : diagram.getBlocks().values()) {
				if (b1 != b2 && b1.getName().contains(b2.getName())) {
					System.out.println("block name error:\n");
					System.out.println(b1.getName() + " contains "
							+ b2.getName() + "\n");
					return false;
				}
			}
		}
		return true;
	}

	// interfaces
	public static String getUdsLocation() {
		return udsLocation;
	}

	public static String getcurrentLoc() {
		return currentLoc;
	}

	public static boolean isCommLinesPrint() {
		return printCommLines;
	}

	public static boolean isTextPrint() {
		return printText;
	}

}
