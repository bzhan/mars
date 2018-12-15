package m2h;

import java.util.ArrayList;

import model.SL_Block;
import model.SL_Diagram;
import model.SL_Line;

public class D_Process {

	protected static String getProcess(SL_Diagram diagram,
			ArrayList<String> aPartition, int i) {
		// reorder the partition
		//System.out.println("%%%%%%%%%%"+aPartition+"%%%%%%%%%%");
		ArrayList<String> thePartition = new ArrayList<String>();
		Boolean loopFlag;
		Boolean freeFlag;
		do {
			loopFlag = false;
			for (String str : aPartition) {
				freeFlag = true;
				for (SL_Line l : diagram.getBlocks().get(str).getDstLines()
						.values()) {
					if (aPartition.contains(l.getSource().getName())) {
						freeFlag = false;
						break;
					}
				}
				if (freeFlag
						|| diagram.getBlocks().get(str).getType()
								.equals("UnitDelay")) {
					thePartition.add(str);
					aPartition.remove(str);
					loopFlag = true;
					break;
				}
			}
		} while (loopFlag);

		// Check if there are loop logic dependences
		if (!aPartition.isEmpty()) {
			System.out.println("logic dependence problem exists!!!");
		}

		// get communications
		String commInStr = "";
		String commOutStr = "";
		for (String str : thePartition) {
			if (diagram.getBlocks().get(str).getParameters().get("commIn") != null) {
				commInStr += diagram.getBlocks().get(str).getParameters()
						.get("commIn")
						+ ";\n";
			}
			if (diagram.getBlocks().get(str).getParameters().get("commOut") != null) {
				commOutStr += diagram.getBlocks().get(str).getParameters()
						.get("commOut")
						+ ";\n";
			}
		}

		// calculate the basic clock
		ArrayList<String> stLists = new ArrayList<String>();
		for (String str : thePartition) {
			stLists.add(diagram.getBlocks().get(str).getParameters().get("st"));
		}
		String basicClock = SampleTime.GCD(stLists);

		// if basicClock is 0, it should be T
		if (basicClock == "0") {
			basicClock = "T";
		}
		SL2HCSP.basicClock = basicClock;

		// initialization
		String init = "";
		for (String str : thePartition) {
			SL_Block b = diagram.getBlocks().get(str);
			if (b.semanticFunctionDiscrete().get("init") != null
					&& !b.semanticFunctionDiscrete().get("init")
							.replaceAll(" ", "").equals("")) {
				init += b.semanticFunctionDiscrete().get("init") + ";\n";
			}
		}
		String initComm1 = "";
		String initComm2 = "";
		for (int j = 0; j < thePartition.size(); j++) {
			String str = thePartition.get((j + 10) % thePartition.size());
			SL_Block b = diagram.getBlocks().get(str);
			if (b.semanticFunctionDiscrete().get("init") != null
					&& !b.semanticFunctionDiscrete().get("init")
							.replaceAll(" ", "").equals("")) {
				// sending initial values
				if (b.getParameters().get("commOut") != null) {
					initComm1 += b.getParameters().get("commOut") + ";\n";
				}
			} else {
				// sending initially computed values
				if (b.getParameters().get("commOut") != null) {
					initComm2 += b.getParameters().get("commOut") + ";\n";
				}
			}
		}

		// computation
		String comp = "";
		if (SampleTime.isAllEqual(stLists)) {// when all sample times equal
			//System.out.println("##########"+thePartition+"##########");
			for (String str : thePartition) {
				//System.out.println("##########"+str+"##########");
				SL_Block b = diagram.getBlocks().get(str);
				//System.out.println("##########"+diagram+"##########");
				if (!b.getParameters().get("st").equals("inf")) {
					//if(!b.semanticFunctionDiscrete().get("fun").contains("+"))
					comp += b.semanticFunctionDiscrete().get("fun") + ";\n";
					
				}
			}
			comp = comp.replaceAll("!","~");
		} else { // general case
			for (String str : thePartition) {
				SL_Block b = diagram.getBlocks().get(str);
				if (!b.getParameters().get("st").equals("inf")) {
					if (!b.getParameters().get("st").equals("0")) {
						comp += "t%" + b.getParameters().get("st") + "-> "
								+ b.semanticFunctionDiscrete().get("fun")
								+ ";\n";
					} else {
						comp += b.semanticFunctionDiscrete().get("fun") + ";\n";
					}
				}
			}
			comp = comp.replaceAll("!","~");
		}

		// replace all in-communicating variable names to input variable names
		if (!SL2HCSP.isCompact) {
			ArrayList<String> commIns = new ArrayList<String>();
			//System.out.println("##########"+thePartition+"##########");
			for (String bstr : thePartition) {
				for (SL_Line l : diagram.getBlocks().get(bstr).getDstLines()
						.values()) {
					if (Comms.isCommLine(l)) {
						if (commIns.contains(l.getChName())) {
							continue;
						} else {
							//System.out.println("##########"+comp+"##########");
							comp = comp.replaceAll(l.getVarName(),
									l.getChName());
							//System.out.println("*********"+comp+"**************");
							commIns.add(l.getChName());
						}
					}
				}
			}
		}

		// wait a basic time
		String timeName = "t" + i;
		// String wait = "temp" + i + ":=" + timeName + "; <<(diff(" + timeName
		// + ")==(Real 1)) && ("
		// + timeName + "<temp" + i + "+(Real " + basicClock + "))>>:(l==(Real "
		// + basicClock
		// + "));";
		String wait = "temp" + i + ":=" + timeName + "; <<(WTrue) && ("
				+ timeName + "<temp" + i + "+(Real " + basicClock
				+ "))>>:(l==(Real " + basicClock + "));";

		// get the process
		String process = "";
		SL2HCSP.sample = basicClock;
		if (!SL2HCSP.isCompact) {
			process = timeName + ":=(Real 0);\n";
			//System.out.println("##########"+process+"##########");
			process += init + initComm1 + commInStr + comp + initComm2;
			/*System.out.println("##########"+init+"##########");
			System.out.println("##########"+initComm1+"##########");
			System.out.println("##########"+commInStr+"##########");
			System.out.println("##########"+comp+"##########");
			System.out.println("##########"+initComm2+"##########");
			System.out.println("##########"+wait+"##########");
			System.out.println("##########"+commInStr+"##########");*/
			process += "(" + wait + commInStr;
			//System.out.println("##########"+process+"##########");
			process += comp;
			if (commOutStr.length() > 2)
				
				{process += commOutStr.subSequence(0, commOutStr.length() - 2)
						+ ")**";
				//System.out.println("#************###"+commOutStr.subSequence(0, commOutStr.length() - 2)+"##########");
				}
		} else {
			process = init + ";;--;;" + comp;
		}

		SL2HCSP.textInit = init + SL2HCSP.textInit;
		SL2HCSP.textRep = comp + SL2HCSP.textRep;
		return process;
	}

	protected static String getProcesses(ArrayList<String> discreteProcesses) {
		String process = "";
		for (String str : discreteProcesses) {
			process += "Discrete Process:\n"
					+ str.replaceAll("Skip;", "").replaceAll("\n\n", "\n")
					+ "\n\n";
		}
		return process;
	}

}
