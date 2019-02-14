package m2h;

import model.SL_Block;
import model.SL_Diagram;
import model.SL_Line;

import java.util.ArrayList;
import java.util.HashMap;

public class C_Process {

	protected static HashMap<String, ArrayList<String>> getProcess(
			SL_Diagram diagram, ArrayList<String> aPartition) {
		// get communications
		String commStr = "";
		int commNum = 0;
		for (String str : aPartition) {
			if (diagram.getBlocks().get(str).getParameters().get("comm") != null) {
				if (!commStr.isEmpty()) {
					commStr += " [] ";
				}
				commStr += diagram.getBlocks().get(str).getParameters()
						.get("comm");
				commNum++;
			}
		}
		setSFLinesNum(diagram, aPartition, commStr);

		ArrayList<String> thePartition = new ArrayList<String>(aPartition);
		HashMap<String, ArrayList<String>> process = getPowerSet(diagram,
				aPartition);
		//System.out.println("*********@@"+thePartition+"@&&&&&&&&&@@");
		ArrayList<String> states = new ArrayList<String>();
		for (int i = 0; i < process.get("mode").size(); i++) {
			/**
			 * Debug by Jian Wang: 19-2-11
			 * if the mode is null, assign an empty string to it
			 */
			if (process.get("mode").get(i) == null) {
				process.get("mode").set(i, " ");
			}
			String str = "(<<(" + process.get("diff").get(i);
			if (!process.get("mode").get(i).isEmpty()) {
				str = str + ") \n\t\t&& (" + process.get("mode").get(i);
			}
			//System.out.println("*********@@"+str+"@&&&&&&&&&@@");
			// replace all in-communicating variable names to input variable
			// names
			ArrayList<String> commIns = new ArrayList<String>();
			for (String bstr : thePartition) {
				for (SL_Line l : diagram.getBlocks().get(bstr).getDstLines()
						.values()) {
					if (Comms.isCommLine(l)) {
						if (commIns.contains(l.getChName())) {
							continue;
						} else {
							str = str.replaceAll(l.getVarName(), l.getChName());
							commIns.add(l.getChName());
						}
					}
				}
			}

			str += ")>>)" + "\n\t" + "|> (" + commStr.replaceAll("\n", "\n\t")
					+ ")";
			//System.out.println("*********@@"+str+"@&&&&&&&&&@@");
			states.add(str);
			//System.out.println("*********@@"+states+"@&&&&&&&&&@@");
			String cstate = "<<diff(t)==(Real 1)," + process.get("diff").get(i)
					+ "\n\t\t && ";
			if (!process.get("mode").get(i).isEmpty()) {
				cstate += process.get("mode").get(i) + "&";
			}
			cstate += "t[<]";
			//System.out.println("*********@@"+states+"@&&&&&&&&&@@");
			SL2HCSP.textCState.add(cstate);
		}
		process.put("state", states);

		// communications
		ArrayList<String> comms = new ArrayList<String>();
		comms.add(commStr);
		comms.add(String.valueOf(commNum));
		process.put("comms", comms);
		//System.out.println("*********@@"+process+"@&&&&&&&&&@@");
		return process;
	}

	private static HashMap<String, ArrayList<String>> getPowerSet(
			SL_Diagram diagram, ArrayList<String> aPartition) {
		HashMap<String, ArrayList<String>> powerStr = new HashMap<String, ArrayList<String>>();
		ArrayList<String> possibleMode = new ArrayList<String>();
		ArrayList<String> possibleDiff = new ArrayList<String>();
		ArrayList<String> Init = new ArrayList<String>();
		//System.out.println("*********@@"+aPartition.size()+"@&&&&&&&&&@@");
		// basic
		if (aPartition.size() <= 1) {
			if (aPartition.size() < 1) {
				System.out.println("an empty partition");
				return powerStr;
			}
			SL_Block b = diagram.getBlocks().get(aPartition.get(0));
			//if (!b.semanticFunctionContinuous().get("init").isEmpty())
			//System.out.println("*********@@"+b.semanticFunctionContinuous()+"@&&&&&&&&&@@");
			
			Init.add(b.semanticFunctionContinuous().get("init"));
			for (int i = 0; i < b.semanticFunctionContinuous().size() / 2; i++) {
				possibleMode.add(b.semanticFunctionContinuous().get(
						String.valueOf(i) + "b"));
				possibleDiff.add(b.semanticFunctionContinuous().get(
						String.valueOf(i)));
			}
			powerStr.put("init", Init);
			powerStr.put("mode", possibleMode);
			powerStr.put("diff", possibleDiff);
			//System.out.println("*********@@"+powerStr+"@&&&&&&&&&@@");
			return powerStr;
			
		}
		// recursion
		SL_Block b = diagram.getBlocks().get(
				aPartition.get(aPartition.size() - 1));
		aPartition.remove(aPartition.size() - 1);
		HashMap<String, ArrayList<String>> powerStr1 = getPowerSet(diagram, //recursion
				aPartition);
		if (b.semanticFunctionContinuous().get("init") == null
				|| b.semanticFunctionContinuous().get("init").isEmpty()) {
			Init.add(powerStr1.get("init").get(0));
		} else {
			if(powerStr1.get("init").get(0)!= null||!powerStr1.get("init").get(0).isEmpty())
				Init.add(powerStr1.get("init").get(0) + ";\n "
						+ b.semanticFunctionContinuous().get("init"));			
		}
		if(Init.get(0).indexOf(";")==0)// deal with [;a;b],change to [a;b]
		{
			String stemp=Init.get(0);
			stemp=stemp.substring(1,stemp.length());
			Init.remove(0);
			Init.add(stemp);
		}
		//System.out.println("*********@@"+Init+"@&&&&&&&&&@@");
		powerStr.put("init", Init);
		ArrayList<String> possibleMode1 = powerStr1.get("mode");
		ArrayList<String> possibleDiff1 = powerStr1.get("diff");
		//System.out.println("*********@@"+possibleMode1+"@&&&&&&&&&@@");
		//if(!possibleMode1.get(0).isEmpty()&&!possibleMode1.get(0).equals("")&&!possibleMode1.get(0).equals(" ")){
			for (int i = 0; i < b.semanticFunctionContinuous().size() / 2; i++) {
				//System.out.println("*********@@"+b.semanticFunctionContinuous().size()+"@&&&&&&&&&@@");
				for (int j = 0; j < possibleMode1.size(); j++) {
					//System.out.println("*********@@iiiiijj"+possibleMode1.size()+"@&&&&&&&&&@@");
					if (i * possibleMode1.size() + j < possibleMode.size()) {
						if (!b.semanticFunctionContinuous()
								.get(String.valueOf(i) + "b").isEmpty()) {
							String b1 = possibleMode1.get(j).replaceAll(" ", "");
							String b2 = (b.semanticFunctionContinuous().get(String
									.valueOf(i) + "b")).replaceAll(" ", "");
							if (!b1.isEmpty() && !b2.isEmpty())
								possibleMode.set(i * possibleMode1.size() + j, b1
										+ "&" + b2);
							else
								possibleMode.set(i * possibleMode1.size() + j, b1
										+ b2);
						} else {
							possibleMode.set(i * possibleMode1.size() + j,
									possibleMode1.get(j));
						}
						possibleDiff.set(
								i * possibleMode1.size() + j,
								possibleDiff1.get(j)
										+ ","
										+ (b.semanticFunctionContinuous()
												.get(String.valueOf(i))));
					} else {
						if (!b.semanticFunctionContinuous()
								.get(String.valueOf(i) + "b").isEmpty()) {
							String b1 = possibleMode1.get(j).replaceAll(" ", "");
							String b2 = (b.semanticFunctionContinuous().get(String
									.valueOf(i) + "b")).replaceAll(" ", "");
							if (!b1.isEmpty() && !b2.isEmpty())
								possibleMode.add(b1 + "&" + b2);
							else
								possibleMode.add(b1 + b2);
						} else {
							possibleMode.add(possibleMode1.get(j));
						}
						possibleDiff.add(possibleDiff1.get(j)
								+ ","
								+ (b.semanticFunctionContinuous().get(String
										.valueOf(i))));
					}
					//System.out.println("*********@@"+possibleDiff+"@&&&&&&&&&@@");
				}
			}
			//}

		// some block do not have any diff and mode, e.g. constant
		if (b.semanticFunctionContinuous().size() < 2) {
			powerStr.put("mode", possibleMode1);
			powerStr.put("diff", possibleDiff1);
		} else {
			powerStr.put("mode", possibleMode);
			powerStr.put("diff", possibleDiff);
		}
		//System.out.println("*********@@"+powerStr.get("mode")+"@&&&&&&&&&@@");
		//System.out.println("*********@@"+powerStr.get("diff")+"@&&&&&&&&&@@");
		return powerStr;
	}

	protected static String getProcesses(
			ArrayList<HashMap<String, ArrayList<String>>> continuousProcesses) {
		String processStr = "";
		for (HashMap<String, ArrayList<String>> process : continuousProcesses) {
			processStr += "Continuous Process:\n";

			// initialization
			if (process.get("init").get(0) != null
					&& !process.get("init").get(0).replaceAll(" ", "")
							.isEmpty()) {
				String str = process.get("init").get(0);
				str = str.replaceAll("; ;", ";");
				if (str.replaceAll(" ", "").startsWith(";")) {
					str = str.substring(str.indexOf(";") + 1, str.length());
				}
				processStr += str + "; \n";
				SL2HCSP.textInit += str + "; \n";
			}

			// initialization for communication
			String commStr = process.get("comms").get(0);
			int commNum = Integer.valueOf(process.get("comms").get(1));
			for (int i = 0; i < commNum - sfLineNum; i++) {
				processStr += "(<<(WTrue && WTrue)>>) |> ("
						+ commStr.replaceAll("\n", "\n\t") + ");\n";
			}

			// repetition
			processStr += "(";
			for (int i = 0; i < process.get("state").size(); i++) {
				String str = process.get("state").get(i);
				if (i < process.get("state").size() - 1) {
					processStr += str + "\n";
				} else {
					processStr += str + ")**\n\n";
				}
			}
		}
		return processStr;
	}

	public static int sfLineNum = 0;

	private static void setSFLinesNum(SL_Diagram diagram,
			ArrayList<String> aPartition, String commStr) {
		// source lines
		for (String str : aPartition) {
			for (ArrayList<SL_Line> sl : diagram.getBlocks().get(str)
					.getSrcLines().values()) {
				boolean goesToSF = false;
				for (int i = 0; i < sl.size(); i++) {
					if (sl.get(i).getTarget().getType().equals("Stateflow"))
						goesToSF = true;
				}
				if (goesToSF)
					sfLineNum++;
			}
		}

		// target lines
		for (SL_Block b : diagram.getBlocks().values()) {
			if (!b.getType().equals("Stateflow"))
				continue;
			int pos = 0;
			while (commStr.indexOf(b.getName(), pos) != -1) {
				pos = commStr.indexOf(b.getName(), pos) + b.getName().length();
				pos = commStr.indexOf(b.getName(), pos) + b.getName().length();
				if (pos == 0) {
					System.out.println("Something wired happened!!!");
				} else {
					// sfLineNum++;
				}
			}
		}
	}

}
