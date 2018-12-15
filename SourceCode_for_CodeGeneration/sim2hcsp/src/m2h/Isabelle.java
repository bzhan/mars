package m2h;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;

import model.S2M;
import model.SL_Diagram;
import model.SL_Block;
import model.SL_Line;
import model.stateflow.SFProcess;

public class Isabelle {

	private static int assertionNum = 0;
	private static int rgNum = 0;
	private static int invNum = 0;
	private static String invDef = "";
	public static String HCSPHOME = System.getenv("MARSHOME") + "/HHLProver";
	private static String ISABELLEHOME = System.getenv("ISABELLEHOME");
	// public static String HCSPHOME = System.getenv("HCSPHOME");
	public static int commN = 4;

	// for compact mode
	private static int domainNums = 0;
	private static int first_condDef=0;

	// private static String domainDef = "";
	// private static String commIDef = "";

	protected static void isabelle(SL_Diagram diagram,
			ArrayList<String> discreteProcesses,
			ArrayList<HashMap<String, ArrayList<String>>> continuousProcesses) {
		String varStr = "";
		String varStr_hcsp = "";//for .hcsp file which using for code generation
		String assertionStr = "";
		String processStr = "";
		String processStr_hcsp = "";//for .hcsp file which using for code generation
		String goal = "";

		if (!SL2HCSP.isCompact) {//without -compact true
			//for isabelle
			varStr = Isabelle.head("varDef", HCSPHOME + "/HHL");
			varStr += Isabelle.channelDef(diagram);
			varStr += Isabelle.channelVarDef(diagram);
			varStr += Isabelle.varDef(diagram, discreteProcesses.size()
					+ S2M.getStateflows().size());
			varStr += Isabelle.commentsDef(diagram);
			varStr += Isabelle.end();
			isabelleWrite("varDef.thy", varStr);
			
			processStr = Isabelle.head("processDef", "assertionDef");
			if (!SFProcess.sfName.isEmpty())
				processStr = Isabelle.head("processDef",
						SFProcess.sfName.get(SFProcess.sfNum - 1) + "PDef");
			processStr += Isabelle.cProcessesDef(continuousProcesses);
			processStr += Isabelle.dProcessesDef(discreteProcesses);
			processStr += Isabelle.wholeProcess(continuousProcesses.size(),
					discreteProcesses.size());
			processStr += Isabelle.end();
			isabelleWrite("processDef.thy", processStr);
			
			//for .hcsp file which using for code generation
			varStr_hcsp=Isabelle.varDef_hcsp(diagram, discreteProcesses.size()
					+ S2M.getStateflows().size());
			if (!Isabelle.channelVarDef_hcsp(diagram).isEmpty())
			    varStr_hcsp +=Isabelle.channelVarDef_hcsp(diagram);
			else
				varStr_hcsp=varStr_hcsp.substring(0, varStr_hcsp.length()-1)+"\n";
			varStr_hcsp +=Isabelle.channelDef_hcsp(diagram);
			//for .hcsp file which using for code generation
			processStr_hcsp = Isabelle.cProcessesDef_hcsp(continuousProcesses);
			processStr_hcsp += Isabelle.dProcessesDef_hcsp(discreteProcesses);
			String wholeProcessStr_hcsp = Isabelle.wholeProcess_hcsp(continuousProcesses.size(),
					discreteProcesses.size());
			isabelleWrite("system.hcsp", wholeProcessStr_hcsp+"\n"+varStr_hcsp+"\n"+processStr_hcsp);

			goal = Isabelle.head("goal", "processDef");
			goal += Isabelle.goal(discreteProcesses.size()
					+ continuousProcesses.size());
			goal += Isabelle.end();
			if (SL2HCSP.rewriteAll)
			isabelleWrite("goal.thy", goal);

			assertionStr = Isabelle.head("assertionDef", "varDef");
			assertionStr += Isabelle.assertionDefAssistC();
			assertionStr += Isabelle.assertionDef();
			assertionStr += Isabelle.end();
		} else {//with -compact true
			varStr = Isabelle.head("varDef", HCSPHOME + "/HHL");
			varStr += Isabelle.varDefC(diagram);
			varStr += Isabelle.commentsDef(diagram);
			varStr += Isabelle.end();
			isabelleWrite("varDef.thy", varStr);

			processStr = Isabelle.head("processDef", "assertionDef");
			if (!SFProcess.sfName.isEmpty())//with stateflow
				processStr = Isabelle.head("processDef",
						SFProcess.sfName.get(SFProcess.sfNum - 1) + "PDef");
			processStr += Isabelle.cProcessesDefC(continuousProcesses);
			processStr += Isabelle.dProcessesDefC(discreteProcesses);
			processStr += Isabelle.wholeProcessC();
			processStr += Isabelle.end();
			isabelleWrite("processDef.thy", processStr);

			goal = Isabelle.head("goal", "processDef");
			goal += Isabelle.goalC();
			goal += Isabelle.end();
			if (SL2HCSP.rewriteAll)
			isabelleWrite("goal.thy", goal);

			assertionStr = Isabelle.head("assertionDef", "varDef");
			assertionStr += Isabelle.assertionDefAssist();
			assertionStr += Isabelle.assertionDef();
			assertionStr += Isabelle.end();
		}

		if (SL2HCSP.rewriteAss || SL2HCSP.rewriteAll)
			isabelleWrite("assertionDef.thy", assertionStr);

		if (SL2HCSP.open)
			try {
				Runtime.getRuntime().exec(
						ISABELLEHOME + "/bin/isabelle emacs "
								+ SL2HCSP.getcurrentLoc() + "goal.thy");
			} catch (IOException e) {
				e.printStackTrace();
			}
		if (SL2HCSP.isTextPrint()) {
			System.out.println(varStr);
			System.out.println(assertionStr);
			System.out.println(processStr);
			System.out.println(goal);
		}
	}

	public static void isabelleWrite(String name, String str) {
		try {
			// Create file
			// String HCSPHOME = System.getenv("HCSPHOME");
			FileWriter fstream = new FileWriter(SL2HCSP.getcurrentLoc() + name);
			BufferedWriter out = new BufferedWriter(fstream);
			out.write(str);
			// Close the output stream
			out.close();
			// Runtime.getRuntime().exec("mv " + name + ".thy " + HCSPHOME);
		} catch (Exception e) {
			System.err.println("Error: " + e.getMessage());
		}
	}

	// define channel names
	protected static String channelDef(SL_Diagram diagram) {
		String str = "(*Define channel names.*)\n";
		ArrayList<SL_Line> commLine = Comms.getCommLine(diagram);
		ArrayList<String> comms = new ArrayList<String>();
		for (SL_Line l : commLine) {
			// ignore the line from constant block
			if (l.getSource().getType().equals("Constant")) {
				continue;
			}
			// ignore when l has already sent to the partition
			if (comms.contains(l.getChName())) {
				continue;
			} else {
				str += "definition Ch_" + l.getChName() + " :: cname where\n"
						+ "\"Ch_" + l.getChName() + " == \'\'Ch_"
						+ l.getChName() + "\'\'\"\n";
				comms.add(l.getChName());
			}
		}
		str = str + "\n";
		return str;
	}
	
	// define channel names for .hcsp file
		protected static String channelDef_hcsp(SL_Diagram diagram) {
			String str = "channelDef ::=";
			ArrayList<SL_Line> commLine = Comms.getCommLine(diagram);
			ArrayList<String> comms = new ArrayList<String>();
			for (SL_Line l : commLine) {
				// ignore the line from constant block
				if (l.getSource().getType().equals("Constant")) {
					continue;
				}
				// ignore when l has already sent to the partition
				if (comms.contains(l.getChName())) {
					continue;
				} else {
					str += "Ch_" +l.getChName() + ";";
					comms.add(l.getChName());
				}
			}
			if (!str.isEmpty())
				str = str.substring(0,str.length()-1) + "\n";
			return str;
		}

	// define receiving var names
	protected static String channelVarDef(SL_Diagram diagram) {
		String str = "(*Define receiving variables.*)\n";
		ArrayList<SL_Line> commLine = Comms.getCommLine(diagram);
		ArrayList<String> comms = new ArrayList<String>();
		for (SL_Line l : commLine) {
			// ignore the line from constant block
			if (l.getSource().getType().equals("Constant")) {
				continue;
			}
			// ignore when l has already sent to the partition
			if (comms.contains(l.getChName())) {
				continue;
			} else {
				if (l.getSource().getOutTypes().get(l.getSrcPort() - 1)) {
					str += "definition " + l.getChName() + " :: exp where\n"
							+ "\"" + l.getChName() + " == BVar \'\'"
							+ l.getChName() + "\'\'\"\n";
				} else {
					str += "definition " + l.getChName() + " :: exp where\n"
							+ "\"" + l.getChName() + " == RVar \'\'"
							+ l.getChName() + "\'\'\"\n";
				}
				comms.add(l.getChName());
			}
		}
		str = str + "\n";
		return str;
	}
	
	// define receiving var names for .hcsp file
		protected static String channelVarDef_hcsp(SL_Diagram diagram) {
			String str = "";
			ArrayList<SL_Line> commLine = Comms.getCommLine(diagram);
			ArrayList<String> comms = new ArrayList<String>();
			for (SL_Line l : commLine) {
				// ignore the line from constant block
				if (l.getSource().getType().equals("Constant")) {
					continue;
				}
				// ignore when l has already sent to the partition
				if (comms.contains(l.getChName())) {
					continue;
				} else {
					if (l.getSource().getOutTypes().get(l.getSrcPort() - 1)) {
						str += l.getChName() + ";";
					} else {
						str += l.getChName() + ";";
					}
					comms.add(l.getChName());
				}
			}
			if (!str.isEmpty())
			str = str.substring(0,str.length()-1) + "\n";
			return str;
		}

	// define local and sending var names
	protected static String varDef(SL_Diagram diagram, int i) {
		String str = "(*Define local and sending variables.*)\n";
		// clock var names for discrete partitions
		for (int j = 0; j <= i; j++) {
			str += "definition t" + j + " :: exp where\n" + "\"t" + j
					+ " == RVar \'\'t" + j + "\'\'\"\n";
			str += "definition temp" + j + " :: exp where\n" + "\"temp" + j
					+ " == RVar \'\'temp" + j + "\'\'\"\n";
		}

		// local and sending var names
		for (SL_Block b : diagram.getBlocks().values()) {
			if (b.getType().equals("Constant")) {
				continue;
			} else if (b.getType().equals("UnitDelay")) {
				String varType = "";
				if (b.getOutTypes().get(0)) {
					varType = "BVar";
				} else {
					varType = "RVar";
				}
				str += "definition " + b.getName() + "_tmp" + " :: exp where\n"
						+ "\"" + b.getName() + "_tmp" + " == " + varType
						+ " \'\'" + b.getName() + "_tmp" + "\'\'\"\n";
			}
			for (ArrayList<SL_Line> ls : b.getSrcLines().values()) {
				String varType = "";
				if (ls.get(0).getSource().getOutTypes()
						.get(ls.get(0).getSrcPort() - 1)) {
					varType = "BVar";
				} else {
					varType = "RVar";
				}
				str += "definition " + ls.get(0).getVarName()
						+ " :: exp where\n" + "\"" + ls.get(0).getVarName()
						+ " == " + varType + " \'\'" + ls.get(0).getVarName()
						+ "\'\'\"\n";
			}
			if (b.getSrcLines().values().isEmpty()) {
				String varType = "RVar";
				str += "definition " + b.getName() + "_1" + " :: exp where\n"
						+ "\"" + b.getName() + "_1" + " == " + varType
						+ " \'\'" + b.getName() + "_1" + "\'\'\"\n";
			}
		}
		str = str + "\n";
		return str;
	}
	
	// define local and sending var names for .hcsp file
		protected static String varDef_hcsp(SL_Diagram diagram, int i) {
			String str = "variableDef ::=";
			// local and sending var names
			for (SL_Block b : diagram.getBlocks().values()) {
				if (b.getType().equals("Constant")) {
					continue;
				} else if (b.getType().equals("UnitDelay")) {
					String varType = "";
					if (b.getOutTypes().get(0)) {
						varType = "BVar";
					} else {
						varType = "RVar";
					}
					str += b.getName() + "_tmp;";
				}
				for (ArrayList<SL_Line> ls : b.getSrcLines().values()) {
					String varType = "";
					if (ls.get(0).getSource().getOutTypes()
							.get(ls.get(0).getSrcPort() - 1)) {
						varType = "BVar";
					} else {
						varType = "RVar";
					}
					str += ls.get(0).getVarName()+ ";" ;
				}
				if (b.getSrcLines().values().isEmpty()) {
					String varType = "RVar";
					str += b.getName() + "_1;";
				}
			}
			return str;
		}

	// define local and sending var names
	protected static String varDefC(SL_Diagram diagram) {
		String str = "(*Define local and sending variables.*)\n";
		// clock var name
		str += "definition t :: exp where\n" + "\"t" + " == RVar \'\'t\'\'\"\n";

		// local and sending var names
		for (SL_Block b : diagram.getBlocks().values()) {
			if (b.getType().equals("Constant")) {
				continue;
			} else if (b.getType().equals("UnitDelay")) {
				String varType = "";
				if (b.getOutTypes().get(0)) {
					varType = "BVar";
				} else {
					varType = "RVar";
				}
				str += "definition " + b.getName() + "_tmp" + " :: exp where\n"
						+ "\"" + b.getName() + "_tmp" + " == " + varType
						+ " \'\'" + b.getName() + "_tmp" + "\'\'\"\n";
			}
			for (ArrayList<SL_Line> ls : b.getSrcLines().values()) {
				String varType = "";
				if (ls.get(0).getSource().getOutTypes()
						.get(ls.get(0).getSrcPort() - 1)) {
					varType = "BVar";
				} else {
					varType = "RVar";
				}
				str += "definition " + ls.get(0).getVarName()
						+ " :: exp where\n" + "\"" + ls.get(0).getVarName()
						+ " == " + varType + " \'\'" + ls.get(0).getVarName()
						+ "\'\'\"\n";
			}
			// if it output nothing
			if (b.getSrcLines().isEmpty()) {
				String varType = "";
				if (b.getOutTypes().get(0))
					varType = "BVar";
				else
					varType = "RVar";
				str += "definition " + b.getName() + "_1" + " :: exp where\n"
						+ "\"" + b.getName() + "_1" + " == " + varType
						+ " \'\'" + b.getName() + "_1" + "\'\'\"\n";
			}
		}
		str = str + "\n";
		return str;
	}

	protected static String commentsDef(SL_Diagram diagram) {
		String str = "(*Definitions in comments, including extra functions defined by user or used during translation.*)\n";

		// extra functions used during translation
		str += "definition max :: \"exp => exp => exp\"\nwhere \"max(a,b) == if formT(a[<]b) then b else a\"";

		InputStream inputstream;
		try {
			inputstream = new FileInputStream(SL2HCSP.getUdsLocation()
					+ "comments");
			BufferedReader bufferreader = new BufferedReader(
					new InputStreamReader(inputstream));

			// analyze the file.
			for (String l1 = bufferreader.readLine(); l1 != null; l1 = bufferreader
					.readLine()) {
				l1 = l1.replaceAll("--", "[minus]");
				l1 = l1.replaceAll("<=", "[leq]");
				l1 = l1.replaceAll(">=", "[geq]");
				l1 = l1.replaceAll("\\+", "[+]");
				l1 = l1.replaceAll("-", "[-]");
				l1 = l1.replaceAll("\\*", "[*]");
				l1 = l1.replaceAll("<", "[<]");
				l1 = l1.replaceAll(">", "[>]");
				l1 = l1.replaceAll("~", "[~]");
				l1 = l1.replaceAll("&", "[&]");
				l1 = l1.replaceAll("\\|", "[|]");
				l1 = l1.replaceAll("-->", "[-->]");
				l1 = l1.replaceAll("<->", "[<->]");
				l1 = l1.replaceAll("===", "[ddd]");
				l1 = l1.replaceAll("==", "[dd]");
				l1 = l1.replaceAll("=", "[=]");
				l1 = l1.replaceAll("\\[minus\\]", "-");
				l1 = l1.replaceAll("\\[leq\\]", "[<=]");
				l1 = l1.replaceAll("\\[geq\\]", "[>=]");
				l1 = l1.replaceAll("\\[dd\\]", "==");
				l1 = l1.replaceAll("\\[ddd\\]", "===");
				if (l1.contains("===")) {
					String varName = l1.substring(0, l1.indexOf("==="))
							.replaceAll(" ", "");
					str += "definition " + varName + " :: exp where\n";
					str += "\"" + (l1.replace("===", "==")) + "\"\n";
				} else if (l1.indexOf("==") > 0) {
					String varName = l1.substring(0, l1.indexOf("=="))
							.replaceAll(" ", "");
					String def = l1
							.substring(l1.indexOf("==") + 2, l1.length());
					str += "definition " + varName + " :: exp where\n";
					str += "\"" + varName + " == if formT(" + def
							+ ") then Bool True else Bool False\"\n";
				} else if (l1.replaceAll(" ", "").equals("")) {
					continue;
				} else {
					str += "User defined comments: Syntax error.\n";
				}
			}
			str = Optimization.deleteConstantVariable(diagram, str) + "\n";
			inputstream.close();
		} catch (FileNotFoundException e) {
			return "";
		} catch (IOException e) {
			e.printStackTrace();
		}
		return str;
	}

	// definition version
	private static String assertionDef() {
		String assertion = "";
		for (int i = 1; i <= assertionNum; i++) {
			assertion += "definition assertion" + i + " :: mid where\n" + "\"";
			assertion += "assertion" + i + " == (WTrue,l[=](Real 0))" + "\"\n";
		}
		assertion += "\n";

		for (int i = 1; i <= rgNum; i++) {
			assertion += "definition rg" + i + " :: fform where\n" + "\"";
			assertion += "rg" + i + " == (l[=](Real 0))" + "\"\n";
		}
		assertion += "\n";
		assertion += invDef + "\n";

		return assertion;
	}

	protected static String assertionDefAssist() {
		String str = "(*Define consts for processes definition.*)\n";
		str += "consts diff :: \"exp => exp\" \n";
		str += "\n";
		return str;
	}

	protected static String assertionDefAssistC() {
		String str = "(*Define consts for processes definition.*)\n";
		str += "consts\n diff :: \"exp => exp\" \n";
		for (int i = 0; i < Isabelle.domainNums; i++) {
			str += " Inv" + i + " :: fform\n";
		}
		str += "\n";
		return str;
	}

	protected static String dProcessesDef(ArrayList<String> discreteProcesses) {
		String dprocess = "(*Define discrete processes*)\n";
		for (int i = 1; i <= discreteProcesses.size(); i++) {
			String str = discreteProcesses.get(i - 1);
			//System.out.print("************"+str+"**********");
			str = str.replaceAll("!", "!!");
			str = str.replaceAll("\\?", "??");
			str = str.replaceAll("==", "[=]");
			// expression and form
			str = str.replaceAll("WTrue", "[WWW]");
			str = str.replaceAll("->", "[IF]");
			str = str.replaceAll("<<", "[langle]");
			str = str.replaceAll(">>", "[rangle]");
			str = str.replaceAll("&&", "[contmid]");
			str = str.replaceAll("\\*\\*", "[repeat]");
			str = str.replaceAll("--", "[minus]");
			str = str.replaceAll("<=", "[leq]");
			str = str.replaceAll(">=", "[geq]");
			str = str.replaceAll("\\+", "[+]");
			str = str.replaceAll("-", "[-]");
			str = str.replaceAll("\\*", "[*]");
			str = str.replaceAll("/", "[**]");
			str = str.replaceAll("<", "[<]");
			str = str.replaceAll(">", "[>]");
			str = str.replaceAll("~", "[~]");
			str = str.replaceAll("&", "[&]");
			str = str.replaceAll("\\|", "[|]");
			str = str.replaceAll("-->", "[-->]");
			str = str.replaceAll("<->", "[<->]");
			str = str.replaceAll("\\[minus\\]", "-");
			str = str.replaceAll("\\[leq\\]", "[<=]");
			str = str.replaceAll("\\[geq\\]", "[>=]");
			str = str.replaceAll("\\[langle\\]", "<");
			str = str.replaceAll("\\[rangle\\]", ">");
			str = str.replaceAll("\\[contmid\\]", "&&");
			str = str.replaceAll("\\[repeat\\]", "*");
			str = str.replaceAll("\\[IF\\]", "->");
			str = str.replaceAll("True", "(Bool True)");
			str = str.replaceAll("False", "(Bool False)");
			str = str.replaceAll("\\[WWW\\]", "WTrue");

			str = str.replaceAll("Skip;", "");
			// separate a big definition to peaces
			boolean repeater = false;
			String def = ""; // assistant processes
			int initNum = 0;
			int indexNum = 1;
			ArrayList<Boolean> isComm = new ArrayList<Boolean>();
			for (; !str.isEmpty(); indexNum++) {
				def += "definition PD" + i + "_" + indexNum
						+ " :: proc where\n\"PD" + i + "_" + indexNum + " == ";
				int maxIndex = getMaxIndex(
						str,
						str.indexOf("Ch") < str.indexOf(";")
								|| str.indexOf(";") < 0
								&& str.indexOf("Ch") >= 0) - 1;
				isComm.add(str.indexOf("Ch") < str.indexOf(";")
						|| str.indexOf(";") < 0 && str.indexOf("Ch") >= 0);

				// when exactly initial part ends, we need to delete "(" and
				// ")*" of repeat part
				if (str.indexOf("temp") < 3 && !repeater) {
					str = str.substring(str.indexOf("temp"), str.length());
					str = str.replaceAll("\\)\\*", "");
					repeater = true;
					initNum = indexNum;
				} else if (str.indexOf("temp") < 200 && !repeater) {
					// initial part, and closed to repeat,
					// remember the process num in initNum
					if (str.indexOf("temp") - 3 <= maxIndex) {
						def += str.substring(0, str.indexOf("temp") - 3)
								+ "\"\n";
						str = str.substring(str.indexOf("temp"), str.length());
						str = str.replaceAll("\\)\\*", "");
						repeater = true;
						initNum = indexNum;
					} else {
						def += str.substring(0, maxIndex) + "\"\n";
						str = str.substring(maxIndex + 1, str.length());
					}
				} else if (str.indexOf(";", 100) > 0) {
					int index = Math.min(maxIndex, str.indexOf(";", 150));
					def += str.substring(0, index) + "\"\n";
					str = str.substring(index + 1, str.length());
				} else {
					// int index = Math.min(maxIndex, str.indexOf(";", 150));
					int index = maxIndex;
					if (index < str.length()) {
						def += str.substring(0, index) + "\"\n";
						str = str.substring(index + 1, str.length());
					} else {
						def += str + "\"\n";
						str = "";
					}
				}
			}
			indexNum--;

			int topCounter = 1;
			int currentNum = 0;
			boolean commStatus = isComm.get(0);
			// up layer process definition for init
			String pdefInit = "definition PD" + i + "_init" + 1
					+ " :: proc where\n\"PD" + i + "_init" + 1 + " == ";
			String pdefInitTop = "definition PD" + i + "_init"
					+ " :: proc where\n\"PD" + i + "_init" + " == PD" + i
					+ "_init" + 1 + ";";
			// int initProgNum = 1;
			for (int j = 1; j <= initNum; j++) {
				if (currentNum < 10 && commStatus == isComm.get(j - 1)) {
					currentNum++;
					pdefInit += "PD" + i + "_" + j + ";";
				} else {
					currentNum = 1;
					topCounter++;
					pdefInit = pdefInit.substring(0, pdefInit.length() - 1)
							+ "\"\n";
					pdefInit += "definition PD" + i + "_init" + topCounter
							+ " :: proc where\n\"PD" + i + "_init" + topCounter
							+ " == PD" + i + "_" + j + ";";
					// initProgNum++;
					pdefInitTop += "PD" + i + "_init" + topCounter + ";";
				}
				commStatus = isComm.get(j - 1);
			}
			pdefInit = pdefInit.substring(0, pdefInit.length() - 1) + "\"\n";
			pdefInitTop = pdefInitTop.substring(0, pdefInitTop.length() - 1)
					+ "\"\n";

			topCounter = 1;
			currentNum = 0;
			commStatus = isComm.get(initNum);
			// up layer process definition for rep
			String pdefRep = "definition PD" + i + "_rep" + 1
					+ " :: proc where\n\"PD" + i + "_rep" + 1 + " == ";
			String pdefRepTop = "definition PD" + i + "_rep"
					+ " :: proc where\n\"PD" + i + "_rep" + " == PD" + i
					+ "_rep" + 1 + ";";
			for (int j = initNum + 1; j <= indexNum; j++) {
				if (currentNum < 10 && commStatus == isComm.get(j - 1)) {
					currentNum++;
					pdefRep += "PD" + i + "_" + j + ";";
				} else {
					currentNum = 1;
					topCounter++;
					pdefRep = pdefRep.substring(0, pdefRep.length() - 1)
							+ "\"\n";
					pdefRep += "definition PD" + i + "_rep" + topCounter
							+ " :: proc where\n\"PD" + i + "_rep" + topCounter
							+ " == PD" + i + "_" + j + ";";
					pdefRepTop += "PD" + i + "_rep" + topCounter + ";";
				}
				commStatus = isComm.get(j - 1);
			}
			pdefRep = pdefRep.substring(0, pdefRep.length() - 1) + "\"\n";
			pdefRepTop = pdefRepTop.substring(0, pdefRepTop.length() - 1)
					+ "\"\n";

			// String pdefInitTop = "";
			// for (int k = 1; k <= initProgNum; k++) {
			// pdefInitTop += "PD" + i + "_init" + k + ";";
			// }

			// pdef is the whole process for this partition
			String pdef = "definition PD" + i + " :: proc where\n\"PD" + i
					+ " == " + "PD" + i + "_init;" + "(PD" + i + "_rep)*\"\n";
			dprocess += def + pdefInit + pdefInitTop + pdefRep + pdefRepTop
					+ pdef + "\n";
		}
		dprocess = addAssertion(dprocess);
		return dprocess;
	}
//for generating .hcsp file
	protected static String dProcessesDef_hcsp(ArrayList<String> discreteProcesses) {
		String dprocess = "";
		for (int i = 1; i <= discreteProcesses.size(); i++) {
			String str = discreteProcesses.get(i - 1);
			//System.out.print("************"+str+"**********");
			str = str.replaceAll("!", "!!");
			str = str.replaceAll("\\?", "??");
			str = str.replaceAll("==", "[=]");
			// expression and form
			str = str.replaceAll("WTrue", "[WWW]");
			str = str.replaceAll("->", "[IF]");
			str = str.replaceAll("<<", "[langle]");
			str = str.replaceAll(">>", "[rangle]");
			str = str.replaceAll("&&", "[contmid]");
			str = str.replaceAll("\\*\\*", "[repeat]");
			str = str.replaceAll("--", "[minus]");
			str = str.replaceAll("<=", "[leq]");
			str = str.replaceAll(">=", "[geq]");
			str = str.replaceAll("\\+", "[+]");
			str = str.replaceAll("-", "[-]");
			str = str.replaceAll("\\*", "[*]");
			str = str.replaceAll("/", "[**]");
			str = str.replaceAll("<", "[<]");
			str = str.replaceAll(">", "[>]");
			str = str.replaceAll("~", "[~]");
			str = str.replaceAll("&", "[&]");
			str = str.replaceAll("\\|", "[|]");
			str = str.replaceAll("-->", "[-->]");
			str = str.replaceAll("<->", "[<->]");
			str = str.replaceAll("\\[minus\\]", "-");
			str = str.replaceAll("\\[leq\\]", "[<=]");
			str = str.replaceAll("\\[geq\\]", "[>=]");
			str = str.replaceAll("\\[langle\\]", "<");
			str = str.replaceAll("\\[rangle\\]", ">");
			str = str.replaceAll("\\[contmid\\]", "&&");
			str = str.replaceAll("\\[repeat\\]", "*");
			str = str.replaceAll("\\[IF\\]", "->");
			str = str.replaceAll("True", "(Bool True)");
			str = str.replaceAll("False", "(Bool False)");
			str = str.replaceAll("\\[WWW\\]", "WTrue");

			str = str.replaceAll("Skip;", "");
			//System.out.println("&&&&&&&&&&&"+str+"$$$$$$$$");
			// separate a big definition to peaces
			boolean repeater = false;
			String def = ""; // assistant processes
			int initNum = 0;
			int indexNum = 1;
			ArrayList<Boolean> isComm = new ArrayList<Boolean>();
			for (; !str.isEmpty(); indexNum++) {
				def += "processDef PD" + i + "_" + indexNum
						+ " ::=";
				int maxIndex = getMaxIndex(
						str,
						str.indexOf("Ch") < str.indexOf(";")
								|| str.indexOf(";") < 0
								&& str.indexOf("Ch") >= 0) - 1;
				isComm.add(str.indexOf("Ch") < str.indexOf(";")
						|| str.indexOf(";") < 0 && str.indexOf("Ch") >= 0);
				//System.out.println("&&&&&&&&&&&"+isComm+"$$$$$$$$");
				// when exactly initial part ends, we need to delete "(" and
				// ")*" of repeat part
				if (str.indexOf("temp") < 3 && !repeater) {
					str = str.substring(str.indexOf("temp"), str.length());
					str = str.replaceAll("\\)\\*", "");
					repeater = true;
					initNum = indexNum;
				} else if (str.indexOf("temp") < 200 && !repeater) {
					// initial part, and closed to repeat,
					// remember the process num in initNum
					if (str.indexOf("temp") - 3 <= maxIndex) {
						def += dProcessesDef_hcsp_terms(str.substring(0, str.indexOf("temp") - 3))
								+ "\n";
						//System.out.println("&&&&&&&&&&&"+def+"$$$$$$$$");
						str = str.substring(str.indexOf("temp"), str.length());
						str = str.replaceAll("\\)\\*", "");
						repeater = true;
						initNum = indexNum;
					} else {
						def += dProcessesDef_hcsp_terms(str.substring(0, maxIndex)) + "\n";
						str = str.substring(maxIndex + 1, str.length());
						//none
					}
				} else if (str.indexOf(";", 100) > 0) {
					int index = Math.min(maxIndex, str.indexOf(";", 150));
					def += dProcessesDef_hcsp_terms(str.substring(0, index)) + "\n";
					//System.out.println("&&&&&&&&&&&"+def+"$$$$$$$$");
					str = str.substring(index + 1, str.length());
					
				} else {
					// int index = Math.min(maxIndex, str.indexOf(";", 150));
					int index = maxIndex;
					if (index < str.length()) {
						def += dProcessesDef_hcsp_terms(str.substring(0, index)) + "\n";
						str = str.substring(index + 1, str.length());
						//none System.out.println("&&&&&&&&&&&"+def+"$$$$$$$$");
					} else {
						def += dProcessesDef_hcsp_terms(str) + "\n";
						str = "";
						//System.out.println("&&&&&&&&&&&"+def+"$$$$$$$$");
					}
				}
			}
			//System.out.println("&&&&&&&&&&&"+def+"$$$$$$$$");
			indexNum--;

			int topCounter = 1;
			int currentNum = 0;
			boolean commStatus = isComm.get(0);
			// up layer process definition for init
			String pdefInit = "processDef PD" + i + "_init" + 1
					+ " ::=";
			String pdefInitTop = "processDef PD" + i + "_init"
					+ " ::= PD" + i
					+ "_init" + 1 + ";";
			// int initProgNum = 1;
			for (int j = 1; j <= initNum; j++) {
				if (currentNum < 10 && commStatus == isComm.get(j - 1)) {
					currentNum++;
					pdefInit += " PD" + i + "_" + j + ";";
				} else {
					currentNum = 1;
					topCounter++;
					pdefInit = pdefInit.substring(0, pdefInit.length() - 1)
							+ "\n";
					pdefInit += "processDef PD" + i + "_init" + topCounter
							+ " ::= PD" + i + "_" + j + ";";
					// initProgNum++;
					pdefInitTop += " PD" + i + "_init" + topCounter + ";";
				}
				commStatus = isComm.get(j - 1);
			}
			pdefInit = pdefInit.substring(0, pdefInit.length() - 1) + "\n";
			pdefInitTop = pdefInitTop.substring(0, pdefInitTop.length() - 1)
					+ "\n";

			topCounter = 1;
			currentNum = 0;
			commStatus = isComm.get(initNum);
			// up layer process definition for rep
			String pdefRep = "processDef PD" + i + "_rep" + 1
					+ " ::= ";
			String pdefRepTop = "processDef PD" + i + "_rep"
					+ " ::= PD" + i
					+ "_rep" + 1 + ";";
			for (int j = initNum + 1; j <= indexNum; j++) {
				if (currentNum < 10 && commStatus == isComm.get(j - 1)) {
					currentNum++;
					pdefRep += " PD" + i + "_" + j + ";";
				} else {
					currentNum = 1;
					topCounter++;
					pdefRep = pdefRep.substring(0, pdefRep.length() - 1)
							+ "\n";
					pdefRep += "processDef PD" + i + "_rep" + topCounter
							+ " ::= PD" + i + "_" + j + ";";
					pdefRepTop += " PD" + i + "_rep" + topCounter + ";";
				}
				commStatus = isComm.get(j - 1);
			}
			pdefRep = pdefRep.substring(0, pdefRep.length() - 1) + "\n";
			pdefRepTop = pdefRepTop.substring(0, pdefRepTop.length() - 1)
					+ "\n";

			// String pdefInitTop = "";
			// for (int k = 1; k <= initProgNum; k++) {
			// pdefInitTop += "PD" + i + "_init" + k + ";";
			// }

			// pdef is the whole process for this partition
			String pdef = "processDef PD" + i + " ::= " + "PD" + i + "_init;" + "PD" + i + "_rep**\n";
			dprocess += def + pdefInit + pdefInitTop + pdefRep + pdefRepTop
					+ pdef + "\n";
		}
		//System.out.println("&&&&&&&&&&&"+dprocess+"$$$$$$$$");
		return dprocess;
	}
	//new function handle dProcessesDef_hcsp_terms
	protected static String dProcessesDef_hcsp_terms(String str1) {
	String term="";
	String str=str1.replaceAll("Real", "").replaceAll(":=", "=").replaceAll("\\[", "").replaceAll("\\]", "").replaceAll("\\*\\*", "/").replaceAll(" ", "");
	//System.out.println("&&&&&&&&&&&"+str+"$$$$$$$$");
	String condDef="";
	if(str.contains("t1="))
	{
		term=str.substring(str.indexOf(";")+1).replaceAll("\n", "");
	}
	else if(str.contains("??")||str.contains("!!"))
	{
		String[] temp=str.split(";");
		ArrayList<String> reChannels = new ArrayList<String>();//receive channels
		ArrayList<String> seChannels = new ArrayList<String>();//send channels
		for (int k=0;k<temp.length;k++)
		{
			if(temp[k].contains("??"))
				reChannels.add(temp[k]);
			else if(temp[k].contains("!!"))
				seChannels.add(temp[k]);
		}
		reChannels.sort(null);
		seChannels.sort(null);
		for(int k=0;k<seChannels.size();k++)
		{
			term+=seChannels.get(k).replaceAll("\n", "")+";";
		}
		for(int k=0;k<reChannels.size();k++)
		{
			term+=reChannels.get(k).replaceAll("\n", "")+";";
		}
	}
	else if(str.contains("temp"))
	{
		term="WAIT"+str.substring(str.indexOf(":(l=")+4, str.indexOf(")", str.indexOf(":(l=")+4)+1);
	}
	else if(str.contains("->"))
	{
		String[] conditions=str.split(",");
		
		for(int m=0;m<conditions.length;m++)
		{
			String[] ifthen=conditions[m].replaceAll("\n", "").split("->");
			term+= "if "+ifthen[0]+" then Cond_"+m+" else SKIP;";
			condDef+="processDef Cond_"+m+ " ::="+ifthen[1]+"\n";
		}
		first_condDef++;
		//term+="\n"+condDef;
		//System.out.println("&&&&&&&&&&&"+term+"$$$$$$$$");
	}
	else
	{
		term=str.replaceAll("\n", "");
	}
	if (term.lastIndexOf(";") >= 0)
		term = term.substring(0, term.lastIndexOf(";"))
				+ "\n";
	//System.out.println("&&&&&&&&&&&"+term+"$$$$$$$$");
	if(first_condDef<=1)
	term+="\n"+condDef;
	return term;
	}
	
	
	protected static String dProcessesDefC(ArrayList<String> discreteProcesses) {
		String dprocess = "(*Define discrete processes*)\n";
		if (discreteProcesses.size() > 1) {
			System.out
					.println("More than one discrete process, please choose not compact.");
			return null;
		}
		//System.out.println( discreteProcesses);
		String str = discreteProcesses.get(0);
		str = str.replaceAll("!", "!!");
		str = str.replaceAll("\\?", "??");
		str = str.replaceAll("==", "[=]");
		// expression and form
		str = str.replaceAll("WTrue", "[WWW]");
		str = str.replaceAll("->", "[IF]");
		str = str.replaceAll("<<", "[langle]");
		str = str.replaceAll(">>", "[rangle]");
		str = str.replaceAll("&&", "[contmid]");
		str = str.replaceAll("\\*\\*", "[repeat]");
		str = str.replaceAll("--", "[minus]");
		str = str.replaceAll("<=", "[leq]");
		str = str.replaceAll(">=", "[geq]");
		str = str.replaceAll("\\+", "[+]");
		str = str.replaceAll("-", "[-]");
		str = str.replaceAll("\\*", "[*]");
		str = str.replaceAll("/", "[**]");
		str = str.replaceAll("<", "[<]");
		str = str.replaceAll(">", "[>]");
		str = str.replaceAll("~", "[~]");
		str = str.replaceAll("&", "[&]");
		str = str.replaceAll("\\|", "[|]");
		str = str.replaceAll("-->", "[-->]");
		str = str.replaceAll("<->", "[<->]");
		str = str.replaceAll("\\[minus\\]", "-");
		str = str.replaceAll("\\[leq\\]", "[<=]");
		str = str.replaceAll("\\[geq\\]", "[>=]");
		str = str.replaceAll("\\[langle\\]", "<");
		str = str.replaceAll("\\[rangle\\]", ">");
		str = str.replaceAll("\\[contmid\\]", "&&");
		str = str.replaceAll("\\[repeat\\]", "*");
		str = str.replaceAll("\\[IF\\]", "->");
		str = str.replaceAll("True", "(Bool True)");
		str = str.replaceAll("False", "(Bool False)");
		str = str.replaceAll("\\[WWW\\]", "WTrue");

		str = str.replaceAll("Skip;", "");

		String Init = str.substring(0, str.indexOf(";;-;;"));
		String Rep = str.substring(str.indexOf(";;-;;") + 5);
		dprocess += "definition PD" + "_Init" + " :: proc where\n\"PD"
				+ "_Init" + " == " + SFProcess.delTail(Init) + "\"\n";
		dprocess += "definition PD" + "_Rep" + " :: proc where\n\"PD" + "_Rep"
				+ " == " + SFProcess.delTail(Rep) + "\"\n\n";

		dprocess = addAssertion(dprocess);
		return dprocess;
	}

	protected static int getMaxIndex(String str, boolean isComm) {
		int max = 0;
		if (str.indexOf(";") < 0) {
			if (str.contains("Ch") && isComm || !str.contains("Ch") && !isComm) {
				max = str.length() + 1;
			} else {
				max = 0;
			}
		} else if (str.indexOf("Ch") < str.indexOf(";") && isComm
				|| str.indexOf("Ch") >= str.indexOf(";") && !isComm) {
			max = getMaxIndex(
					str.substring(str.indexOf(";") + 1, str.length()), isComm)
					+ str.indexOf(";") + 1;
		} else {
			max = 0;
		}
		return max;
	}

	protected static String cProcessesDef(
			ArrayList<HashMap<String, ArrayList<String>>> continuousProcesses) {
		String cprocess = "(*Define continuous processes*)\n";
		//System.out.println("&&&&&&&&&&&"+continuousProcesses+"$$$$$$$$");
		for (int i = 1; i <= continuousProcesses.size(); i++) {
			//System.out.println("&&&&&&&&&&&"+continuousProcesses.size()+"$$$$$$$$");
			HashMap<String, ArrayList<String>> process = continuousProcesses
					.get(i - 1);

			// get initial and repetition string
			String init = "";
			ArrayList<String> rep = new ArrayList<String>();
			if (process.get("init").get(0) != null
					&& !process.get("init").get(0).replaceAll(" ", "")
							.isEmpty()) {
				init = process.get("init").get(0) + "\n";
			}
			//System.out.println("&&&&&&&&&&&"+process.get("init")+"$$$$$$$$");
			// if init start with ";"
			if (init.startsWith(";"))
				init = init.substring(init.indexOf(";") + 1, init.length());
			rep = process.get("state");
			//System.out.println("&&&&&&&&&&&"+process.get("state")+"$$$$$$$$");
			// for initialization
			init = init.replaceAll("==", "[=]");
			init = init.replaceAll("True", "(Bool True)");
			init = init.replaceAll("False", "(Bool False)");
			init = init.replaceAll("\\+", "[+]");
			//System.out.println("&&&&&&&&&&&"+init+"$$$$$$$$");
			// for repetition
			//System.out.println("&&&&&&&&&&&"+rep+"$$$$$$$$");
			for (int j = 0; j < rep.size(); j++) {
				//System.out.println("&&&&&&&&&&&"+rep.get(j)+"$$$$$$$$");
				String state = rep.get(j);
				state = state.replaceAll("!", "!!");
				state = state.replaceAll("\\?", "??");
				state = state.replaceAll("==", "[=]");
				// expression and form
				state = state.replaceAll("WTrue", "[WWW]");
				state = state.replaceAll("->", "[IF]");
				state = state.replaceAll("<<", "[langle]");
				state = state.replaceAll(">>", "[rangle]");
				state = state.replaceAll("\\|>", "[interrupt]");
				state = state.replaceAll("/\\\\", "[domain]");
				state = state.replaceAll("&&", "[contmid]");
				state = state.replaceAll("\\*\\*", "[repeat]");
				state = state.replaceAll("--", "[minus]");
				state = state.replaceAll("<=", "[leq]");
				state = state.replaceAll(">=", "[geq]");
				state = state.replaceAll("\\[\\[leq\\]\\]", "[leq]");
				state = state.replaceAll("\\[\\[geq\\]\\]", "[geq]");
				state = state.replaceAll("\\+", "[+]");
				state = state.replaceAll("-", "[-]");
				state = state.replaceAll("\\*", "[*]");
				state = state.replaceAll("/", "[**]");
				state = state.replaceAll("<", "[<]");
				state = state.replaceAll(">", "[>]");
				state = state.replaceAll("\\[\\[<\\]\\]", "[<]");
				state = state.replaceAll("\\[\\[>\\]\\]", "[>]");
				state = state.replaceAll("~", "[~]");
				state = state.replaceAll("&", "[&]");
				state = state.replaceAll("\\|", "[|]");
				state = state.replaceAll("-->", "[-->]");
				state = state.replaceAll("<->", "[<->]");
				state = state.replaceAll("\\[minus\\]", "-");
				state = state.replaceAll("\\[leq\\]", "[<=]");
				state = state.replaceAll("\\[geq\\]", "[>=]");
				state = state.replaceAll("\\[langle\\]", "<");
				state = state.replaceAll("\\[rangle\\]", ">");
				state = state.replaceAll("\\[contmid\\]", "&&");
				state = state.replaceAll("\\[domain\\]",
						Matcher.quoteReplacement("/\\"));
				state = state.replaceAll("\\[interrupt\\]", "[[[[>");
				state = state.replaceAll("\\[repeat\\]", "*");
				state = state.replaceAll("\\[IF\\]", "->");
				state = state.replaceAll("True", "(Bool True)");
				state = state.replaceAll("False", "(Bool False)");
				state = state.replaceAll("\\[WWW\\]", "WTrue");

				// different equations
				state = state.replaceAll(",", " [&] ");
				state = state.replaceAll("\\[\\]", "[[");
				state = state.replaceAll("/\\\\", "[&]");
				state = addRg(state, "\\>\\)", ">", ")");
				state = state.replaceAll("Real", "Real ");
				//System.out.println("&&&&&&&&&&&"+rep.get(j)+"$$$$$$$$");
				rep.set(j, state);
			}
			//System.out.println("&&&&&&&&&&&"+rep.get(1)+"$$$$$$$$");
			String def = ""; // assistant pdefInites
			// define initialization
			String pdefInit = "definition PC" + i + "_init"
					+ " :: proc where\n\"PC" + i + "_init" + " == ";
			int j = 1;
			//System.out.println("&&&&&&&&&&&"+init+"$$$$$$$$");
			for (; !init.isEmpty(); j++) {
				def += "definition PC" + i + "_" + j + " :: proc where\n\"PC"
						+ i + "_" + j + " == ";
				if (init.indexOf(";", 150) > 0) {//why 150 ?????????
					def += init.substring(0, init.indexOf(";", 150)) + "\"\n";
					pdefInit += "PC" + i + "_" + j + ";";
					init = init.substring(init.indexOf(";", 150) + 11,
							init.length());
				} else {
					def += init + "\"\n";
					//System.out.println("&&&&&&&&&&&"+pdefInit+"$$$$$$$$");
					pdefInit += "PC" + i + "_" + j + ";";
					//System.out.println("&&&&&&&&&&&"+pdefInit+"$$$$$$$$");
					init = "";
				}
			}

			// initialization for communication
			String commStr = process.get("comms").get(0).replaceAll("!", "!!")
					.replaceAll("\\?", "??").replaceAll("\\[\\]", "[[");
			def += "definition commI" + i + " :: proc where\n" + "\"" + "commI"
					+ i + " == " + commStr + "\"\n";
			commN = Integer.valueOf(process.get("comms").get(1));
			int commNum = Integer.valueOf(process.get("comms").get(1))
					- C_Process.sfLineNum;
			//System.out.println("&&&&&&&&&&&"+j+"$$$$$$$$");
			for (int k = 0; k < commNum; j++) {
				def += "definition PC" + i + "_" + j + " :: proc where\n\"PC"
						+ i + "_" + j + " == ";
				pdefInit += "PC" + i + "_" + j + ";";
				for (int l = 0; l < 6 && k < commNum; l++) {
					def += "(<WTrue && WTrue>:WTrue) [[> (commI" + i + ")";
					if (l < 5 && k < commNum - 1)
						def += ";\n";
					k++;
				}
				def += "\"\n";
			}
			if (pdefInit.lastIndexOf(";") >= 0)
				pdefInit = pdefInit.substring(0, pdefInit.lastIndexOf(";"))
						+ "\"\n";
			else
				pdefInit = "";

			//System.out.println("&&&&&&&&&&&"+pdefInit+"$$$$$$$$");
			// define repetition
			String pdefRep = "definition PC" + i + "_rep"
					+ " :: proc where\n\"PC" + i + "_rep" + " == ";
			//System.out.println("&&&&&&&&&&&"+rep.size()+"$$$$$$$$");
			for (int k = j; k < j + rep.size(); k++) {
				// String inv = rep.get(k - j).substring(2, rep.get(k -
				// j).indexOf("&&"));
				//System.out.println("&&&&&&&&&&&"+rep+"$$$$$$$$");
				String domain = rep.get(k - j).substring(
						rep.get(k - j).indexOf("&&") + 2,
						rep.get(k - j).indexOf(">:"));
				String rg = rep.get(k - j).substring(
						rep.get(k - j).indexOf(">:") + 2,
						rep.get(k - j).indexOf("[[[[>"));
				//System.out.println("&&&&&&&&&&&"+rg+"$$$$$$$$");
				// String commI = rep.get(k - j).substring(
				// rep.get(k - j).indexOf("[[>") + 3,
				// rep.get(k - j).length());
				// invDef += "definition inv" + (++invNum) + " :: fform where\n"
				// + "\"" + "inv"
				// + invNum + " == " + inv + "\"\n";
				//System.out.println("&&&&&&&&&&&"+invNum+"$$$$$$$$");
				invDef += "definition inv" + (++invNum) + " :: fform where\n"
						+ "\"" + "inv" + invNum + " == WTrue\"\n";
				//def += "definition inv" + invNum + " :: fform where\n"
				//		+ "\"" + "inv" + invNum + " == WTrue\"\n";
				def += "definition domain" + (invNum) + " :: fform where\n"
						+ "\"" + "domain" + invNum + " == " + domain + "\"\n";
				def += "definition PC" + i + "_" + k + " :: proc where\n\"PC"
						+ i + "_" + k + " == (<inv" + invNum + " && domain"
						+ invNum + ">:" + rg + "[[>" + "commI" + i + "\"\n";
				if (k < j + rep.size() - 1)
					pdefRep += "PC" + i + "_" + k + ";";
				else
					pdefRep += "PC" + i + "_" + k + "\"\n";
			}

			// pdef is the whole process for this partition
			String pdef = "definition PC" + i + " :: proc where\n\"PC" + i
					+ " == " + "PC" + i + "_init" + ";(PC" + i + "_rep)*\"\n";
			cprocess += def + pdefInit + pdefRep + pdef + "\n";
		}
		cprocess = addAssertion(cprocess);
		return cprocess;
	}
	
	//for generating the .hcsp file
	protected static String cProcessesDef_hcsp(
			ArrayList<HashMap<String, ArrayList<String>>> continuousProcesses) {
		String cprocess = "";
		//System.out.println("&&&&&&&&&&&"+continuousProcesses+"$$$$$$$$");
		for (int i = 1; i <= continuousProcesses.size(); i++) {
			//System.out.println("&&&&&&&&&&&"+continuousProcesses.size()+"$$$$$$$$");
			HashMap<String, ArrayList<String>> process = continuousProcesses
					.get(i - 1);

			// get initial and repetition string
			String init = "";
			ArrayList<String> rep = new ArrayList<String>();
			if (process.get("init").get(0) != null
					&& !process.get("init").get(0).replaceAll(" ", "")
							.isEmpty()) {
				init = process.get("init").get(0) + "\n";
			}
			
			// if init start with ";"
			if (init.startsWith(";"))
				init = init.substring(init.indexOf(";") + 1, init.length());
			init = init.replaceAll(":=", "=");
			init = init.replaceAll("\\(Real ", "");
			init = init.replaceAll("\\)", "");
			init = init.replaceAll("\n", "");
			//System.out.println("&&&&&&&&&&&"+init+"$$$$$$$$");
			rep = process.get("state");
			// for repetition
			//System.out.println("&&&&&&&&&&&"+rep+"$$$$$$$$");
			for (int j = 0; j < rep.size(); j++) {
				//System.out.println("&&&&&&&&&&&"+rep.get(j)+"$$$$$$$$");
				String state = rep.get(j);
				state = state.replaceAll("!", "!!");
				state = state.replaceAll("\\?", "??");
				state = state.replaceAll("==", "[=]");
				// expression and form
				state = state.replaceAll("WTrue", "[WWW]");
				state = state.replaceAll("->", "[IF]");
				state = state.replaceAll("<<", "[langle]");
				state = state.replaceAll(">>", "[rangle]");
				state = state.replaceAll("\\|>", "[interrupt]");
				state = state.replaceAll("/\\\\", "[domain]");
				state = state.replaceAll("&&", "[contmid]");
				state = state.replaceAll("\\*\\*", "\\/");
				state = state.replaceAll("--", "[minus]");
				state = state.replaceAll("<=", "[leq]");
				state = state.replaceAll(">=", "[geq]");
				state = state.replaceAll("\\[\\[leq\\]\\]", "[leq]");
				state = state.replaceAll("\\[\\[geq\\]\\]", "[geq]");
				state = state.replaceAll("\\+", "[+]");
				state = state.replaceAll("-", "[-]");
				state = state.replaceAll("\\*", "[*]");
				state = state.replaceAll("/", "[**]");
				state = state.replaceAll("<", "[<]");
				state = state.replaceAll(">", "[>]");
				state = state.replaceAll("\\[\\[<\\]\\]", "[<]");
				state = state.replaceAll("\\[\\[>\\]\\]", "[>]");
				state = state.replaceAll("~", "[~]");
				state = state.replaceAll("&", "[&]");
				state = state.replaceAll("\\|", "[|]");
				state = state.replaceAll("-->", "[-->]");
				state = state.replaceAll("<->", "[<->]");
				state = state.replaceAll("\\[minus\\]", "-");
				state = state.replaceAll("\\[leq\\]", "[<=]");
				state = state.replaceAll("\\[geq\\]", "[>=]");
				state = state.replaceAll("\\[langle\\]", "<");
				state = state.replaceAll("\\[rangle\\]", ">");
				state = state.replaceAll("\\[contmid\\]", "&&");
				state = state.replaceAll("\\[domain\\]",
						Matcher.quoteReplacement("/\\"));
				state = state.replaceAll("\\[interrupt\\]", "[[[[>");
				state = state.replaceAll("\\[repeat\\]", "*");
				state = state.replaceAll("\\[IF\\]", "->");
				state = state.replaceAll("True", "(Bool True)");
				state = state.replaceAll("False", "(Bool False)");
				state = state.replaceAll("\\[WWW\\]", "WTrue");

				// different equations
				state = state.replaceAll(",", " [&] ");
				state = state.replaceAll("\\[\\]", "[[");
				state = state.replaceAll("/\\\\", "[&]");
				state = addRg(state, "\\>\\)", ">", ")");
				state = state.replaceAll("Real", "Real ");
				state = state.replaceAll("\\*\\*", "\\/");
				//System.out.println("&&&&&&&&&&&"+state+"$$$$$$$$");
				rep.set(j, state);
			}
			//System.out.println("&&&&&&&&&&&"+rep.get(1)+"$$$$$$$$");
			String def = ""; // assistant pdefInites
			// define initialization
			String pdefInit = "processDef PC" + i + "_init::=";
			int j = 1;
			//System.out.println("&&&&&&&&&&&"+init+"$$$$$$$$");
			for (; !init.isEmpty(); j++) {
				def += "processDef PC" + i + "_" + j + " ::=";
					def += init + "\n";
					//System.out.println("&&&&&&&&&&&"+pdefInit+"$$$$$$$$");
					pdefInit += "PC" + i + "_" + j + ";";
					//System.out.println("&&&&&&&&&&&"+pdefInit+"$$$$$$$$");
					init = "";				
			}

			// initialization for communication and communication has orders
			String commStr = process.get("comms").get(0).replaceAll("!", "!!")
					.replaceAll("\\?", "??").replaceAll("\\[\\]", "[[").replaceAll(" ", "");
			String[] temp=commStr.split("\\[\\[");
			commStr="";
			ArrayList<String> reChannels = new ArrayList<String>();//receive channels
			ArrayList<String> seChannels = new ArrayList<String>();//send channels
			for (int k=0;k<temp.length;k++)
			{
				if(temp[k].contains("??"))
					reChannels.add(temp[k]);
				else if(temp[k].contains("!!"))
					seChannels.add(temp[k]);
			}
			reChannels.sort(null);
			seChannels.sort(null);
			for(int k=0;k<reChannels.size();k++)
			{
				commStr+=reChannels.get(k)+";";
			}
			for(int k=0;k<seChannels.size();k++)
			{
				commStr+=seChannels.get(k)+";";
			}
			if (commStr.lastIndexOf(";") >= 0)
				commStr = commStr.substring(0, commStr.lastIndexOf(";"))
						+ "\n";
			else
				commStr = "";
			//System.out.println("&&&&&&&&&&&"+commStr+"$$$$$$$$");
			def += "processDef commI" + i + " ::=" + commStr;
			pdefInit += "commI" + i+"\n";
/*			commN = Integer.valueOf(process.get("comms").get(1));
			int commNum = Integer.valueOf(process.get("comms").get(1))
					- C_Process.sfLineNum;
			//System.out.println("&&&&&&&&&&&"+commNum+"$$$$$$$$");
			for (int k = 0; k < commNum; j++) {
				def += "processDef PC" + i + "_" + j + " ::=";
				pdefInit += "PC" + i + "_" + j + ";";
				for (int l = 0; l < 6 && k < commNum; l++) {
					def += "commI" + i;
					if (l < 5 && k < commNum - 1)
						def += ";\n";
					k++;
				}
				def += "\n";
			}*/
/*			if (pdefInit.lastIndexOf(";") >= 0)
				pdefInit = pdefInit.substring(0, pdefInit.lastIndexOf(";"))
						+ "\n";
			else
				pdefInit = "";*/

			//System.out.println("&&&&&&&&&&&"+pdefInit+"$$$$$$$$");
			// define repetition
			String pdefRep = "processDef PC" + i + "_rep"
					+ " ::=";
			//System.out.println("&&&&&&&&&&&"+def+"$$$$$$$$");
			for (int k = j; k < j + rep.size(); k++) {
				// String inv = rep.get(k - j).substring(2, rep.get(k -
				// j).indexOf("&&"));
				//System.out.println("&&&&&&&&&&&"+rep+"$$$$$$$$");
				String domain = rep.get(k - j).substring(
						rep.get(k - j).indexOf("&&") + 2,
						rep.get(k - j).indexOf("[>]:")).replaceAll("\\[", "").replaceAll("\\]", "").replaceAll("Real ", "");
				domain=domain.replaceAll(" ", "");
				if(domain.isEmpty()||domain.equals("()"))
					domain="(true)";
				//System.out.println("&&&&&&&&&&&"+domain+"$$$$$$$$");
		
				String dotstr_1 = rep.get(k - j).substring(
						rep.get(k - j).indexOf("diff"),
						rep.get(k - j).indexOf("&&"));
				dotstr_1=dotstr_1.substring(0, dotstr_1.lastIndexOf(")"));
				//System.out.println("&&&&&&&&&&&"+dotstr_1+"$$$$$$$$");
				String[] dotstr_2=dotstr_1.split("[[&]]");
				String dotstr_pre="DOT(";
				String dotstr_pos="={";
				for(int m=0;m<dotstr_2.length;m++)
				{
					String dotstr_temp=dotstr_2[m].replaceAll(" ", "").replaceAll("Real", "").replaceAll("\\[", "").replaceAll("\\]", "");
					dotstr_pre+=dotstr_temp.substring(dotstr_temp.indexOf("diff(")+5, dotstr_temp.indexOf(")="))+",";
					dotstr_pos+=dotstr_temp.substring(dotstr_temp.indexOf("=")+1)+",";
				}
				if (dotstr_pre.lastIndexOf(",") >= 0)
					dotstr_pre = dotstr_pre.substring(0, dotstr_pre.lastIndexOf(","))+ ")";
				else
					dotstr_pre = "";
				if (dotstr_pos.lastIndexOf(",") >= 0)
					dotstr_pos = dotstr_pos.substring(0, dotstr_pos.lastIndexOf(",")).replaceAll("\n", "").replaceAll("\t", "")+ "}";
				else
					dotstr_pos = "";
				String dotstr=dotstr_pre+dotstr_pos;
				//System.out.println("&&&&&&&&&&&"+dotstr+"$$$$$$$$");
				
				String commI = rep.get(k - j).substring(
				rep.get(k - j).indexOf("(Ch")+1,
				rep.get(k - j).lastIndexOf(")")).replaceAll("!!!!", "!!").replaceAll("\\?\\?\\?\\?", "??");
				String[] temp_2=commI.split("\\[\\[");
				ArrayList<String> reChannels_2 = new ArrayList<String>();//receive channels
				ArrayList<String> seChannels_2 = new ArrayList<String>();//send channels
				for (int m=0;m<temp_2.length;m++)
				{
					if(temp_2[m].contains("??"))
						reChannels_2.add(temp_2[m]);
					else if(temp_2[m].contains("!!"))
						seChannels_2.add(temp_2[m]);
				}
				reChannels_2.sort(null);
				seChannels_2.sort(null);
				String instr_pre=seChannels_2.get(0).replaceAll("\t", "").replaceAll("\n", "");
				seChannels_2.remove(0);
				String instr_pos="";
				for (int m=0;m<seChannels_2.size();m++)
				{
					instr_pos+=seChannels_2.get(m).replaceAll("\t", "").replaceAll("\n", "")+";";
				}
				for (int m=0;m<reChannels_2.size();m++)
				{
					instr_pos+=reChannels_2.get(m).replaceAll("\t", "").replaceAll("\n", "")+";";
				}
				if (instr_pos.lastIndexOf(";") >= 0)
					instr_pos = instr_pos.substring(0, instr_pos.lastIndexOf(";"))
							+ "\n";
				else
					dotstr_pos = "";
				def += "processDef interrupt_" + (++invNum)+"_proc ::= "+instr_pos.replaceAll(" ", "");
				
				String instr="INTERRUPT({"+instr_pre+"}{interrupt_"+ (invNum) + "_proc})";
				//System.out.println("&&&&&&&&&&&"+instr+"$$$$$$$$");
				def += "processDef domain_" + (invNum) + "_proc ::= "+dotstr+" DOMAIN(TRUE) "+instr+"\n";
				
				def += "processDef PC" + i + "_" + k + " ::= if "+domain+" then domain_"+invNum+"_proc "+"else SKIP \n";

				if (k < j + rep.size() - 1)
					pdefRep += "PC" + i + "_" + k + ";";
				else
					pdefRep += "PC" + i + "_" + k + "\n";
			}

			// pdef is the whole process for this partition
			String pdef = "processDef PC" + i + " ::=" + "PC" + i + "_init" + ";PC" + i + "_rep**\n";
			cprocess += def + pdefInit + pdefRep + pdef + "\n";
			//System.out.println("&&&&&&&&&&&"+cprocess+"$$$$$$$$");
		}
		return cprocess;
	}

	protected static String cProcessesDefC(
			ArrayList<HashMap<String, ArrayList<String>>> continuousProcesses) {
		String cprocess = "(*Define continuous processes*)\n";
		if (continuousProcesses.size() > 1) {
			System.out
					.println("More than one continuous process, please choose not compact.");
			return null;
		}
		HashMap<String, ArrayList<String>> process = continuousProcesses.get(0);

		// Init
		cprocess += "definition PC_Init :: proc where\n\"PC_Init" + " == "
				+ process.get("init").get(0) + "\"\n";
		//System.out.println("&&&&&&&&&&&"+cprocess+"$$$$$$$$");

		String pdiff = "";
		Isabelle.domainNums = process.get("mode").size();
		String t = SL2HCSP.sample;
		for (int i = 1; i <= process.get("mode").size(); i++) {
			invDef += "definition Inv" + (++invNum) + " :: fform where\n"
					+ "\"" + "Inv" + invNum + " == WTrue\"\n";
			cprocess += "\n(*Diff: " + process.get("diff").get(i - 1) + "*)\n";
			//System.out.println("&&&&&&&&&&&"+process.get("diff").get(i - 1)+"$$$$$$$$\n");
			String odiff = "";//odiff only save diff expressions
				String diff[]=process.get("diff").get(i-1).split(",");
				for( int j=0;j<diff.length;j++)
				{
					if(diff[j].contains("diff(")&&!odiff.contains(diff[j]))
					{
						if(odiff==null||odiff.isEmpty())
						{
							odiff=odiff+diff[j];
						}
						else
						{
							odiff=odiff+","+diff[j];
						}
						
					}
				}
			//System.out.println("&&&&&&&&&&&"+tempprocess+"$$$$$$$$\n");
			//String odiff = process.get("diff").get(i - 1);
			//System.out.println("&&&&&&&&&&&"+odiff+"$$$$$$$$");
			String wdiff1 = "", wdiff2 = "";
			while (odiff.indexOf(',') >= 0) {
				String adiff = odiff.substring(0, odiff.indexOf(','));
				odiff = odiff.substring(odiff.indexOf(',') + 1);
				wdiff1 = wdiff1
						+ adiff.substring(0, adiff.indexOf("="))
								.replaceAll("diff\\(", "").replaceAll("\\)", "")
						+ ",";
				wdiff2 = wdiff2
						+ adiff.substring(adiff.indexOf("=") + 2).replaceAll(
								"Real", "Real ") + ",";
			}
			wdiff1 = wdiff1
					+ odiff.substring(0, odiff.indexOf("="))
							.replaceAll("diff\\(", "").replaceAll("\\)", "") + ",t";
			wdiff2 = wdiff2
					+ odiff.substring(odiff.indexOf("=") + 2).replaceAll(
							"Real", "Real ") + ",1";
			//System.out.println("&&&&&&&&&&&"+wdiff2+"$$$$$$$$");
			String pmode=process.get("mode").get(i - 1);
			//System.out.println("&&&&&&&&&&&"+pmode+"$$$$$$$$");
			wdiff2=wdiff2.replaceAll("Real ", "");
			pmode=pmode.replaceAll("Real", "Real ");
			pmode=pmode.replaceAll("~", "[~]");
			pmode=pmode.replaceAll("&", "[&]");
			pmode = pmode.replaceAll("<=", "[leq]");
			pmode = pmode.replaceAll(">=", "[geq]");
			pmode=pmode.replaceAll(">", "[>]");
			pmode=pmode.replaceAll("<", "[<]");
			pmode=pmode.replaceAll("\\[geq\\]", "[>=]");
			pmode=pmode.replaceAll("\\[leq\\]", "[<=]");
			pmode=pmode.replaceAll("==", "[=]");
			//System.out.println("&&&&&&&&&&&"+pmode+"$$$$$$$$");
			String wdiff = "(%''" + wdiff1 + "'', ''" + wdiff2 + "''%)";
			cprocess += "definition PC_Diff" + i + " :: proc where\n\"PC_Diff"
					+ i + " == <" + wdiff + " && Inv" + i + " && ("
					+ pmode
					+ "[&] t [<] (Real " + t + ")" + ")>: WTrue\"\n";
			pdiff += "PC_Diff" + i + ";";
		}
			pdiff = pdiff.substring(0, pdiff.length() - 1);
			cprocess=cprocess.replaceAll("\\[\\[", "[").replaceAll("\\]\\]", "]");
			//System.out.println("&&&&&&&&&&&"+cprocess+"$$$$$$$$");
		cprocess += "\ndefinition PC_Diff :: proc where\n\"PC_Diff" + " == "
				+ pdiff + "\"\n\n";

		cprocess = addAssertion(cprocess);
		return cprocess;
	}

	protected static String wholeProcess(int pc, int pd) {
		String pdef = "(*Define the whole process.*)\n";
		pdef += "definition P" + " :: proc where\n\"P" + " == PC1";
		for (int i = 2; i <= pc; i++) {
			pdef += "||" + "PC" + i;
		}
		for (int i = 1; i <= pd; i++) {
			pdef += "||" + "PD" + i;
		}
		// add stateflow
		for (int i = 1; i <= SFProcess.sfNum; i++) {
			pdef += "||" + "P" + SFProcess.sfName.get(i - 1);
		}
		pdef += "\"\n";
		return pdef;
	}
	//for generating .hcsp file
	protected static String wholeProcess_hcsp(int pc, int pd) {
		String pdef = "systemDef ";
		pdef += "P::= PC1";
		for (int i = 2; i <= pc; i++) {
			pdef += "||" + "PC" + i;
		}
		for (int i = 1; i <= pd; i++) {
			pdef += "||" + "PD" + i;
		}
		// add stateflow
		for (int i = 1; i <= SFProcess.sfNum; i++) {
			pdef += "||" + "P" + SFProcess.sfName.get(i - 1);
		}
		pdef += "\n";
		return pdef;
	}

	protected static String wholeProcessC() {
		String pdef = "(*Define the whole process.*)\n";
		pdef += "definition P"
				+ " :: proc where\n\"P"
				+ " == (PC_Init;PD_Init;t:=(Real 0));(PC_Diff;t:=(Real 0);PD_Rep)*\"\n";
		pdef = addAssertion(pdef);
		return pdef;
	}

	protected static String goal(int n) {
		String str = "(*Assistance for defining goal, user may need to modify it for proof.*)\n";
		str += "consts \n";
		str += "pre :: fform \n";
		str += "post :: fform \n";
		str += "H :: fform \n";
		str += "\n";
		str += "(*Goal for the whole process.*)\n";
		String pre = "";
		String post = "";
		String H = "";
		for (int i = 0; i < n; i++) {
			pre += "pre,";
			post += "post,";
			H += "H,";
		}
		pre = pre.substring(0, pre.length() - 1);
		post = post.substring(0, post.length() - 1);
		H = H.substring(0, H.length() - 1);
		str += "lemma goal : \"{" + pre + "} P {" + post + "; " + H
				+ "}\"\nsorry\n\n";
		return str;
	}

	protected static String goalC() {
		String str = "(*Assistance for defining goal, user may need to modify it for proof.*)\n";
		str += "consts \n";
		str += "pre :: fform \n";
		str += "post :: fform \n";
		str += "H :: fform \n";
		str += "\n";
		str += "(*Goal for the whole process.*)\n";
		String pre = "pre";
		String post = "post";
		String H = "H";
		str += "lemma goal : \"{" + pre + "} P {" + post + "; " + H
				+ "}\"\nsorry\n\n";
		return str;
	}

	public static String head(String name, String imports) {
		String str = "theory " + name + "\n";
		str += "\timports \"" + imports + "\"\n";
		str += "begin\n\n";
		return str;
	}

	public static String end() {
		String str = "end\n";
		return str;
	}

	protected static String addAssertion(String str) {
		str = str.replaceAll(";", ";;");
		while (str.indexOf(";;") >= 0) {
			assertionNum++;
			str = str.replaceFirst(";;", ";assertion" + assertionNum + ";");
		}
		return str;
	}

	protected static String addRg(String str, String oldStr, String newLeft,
			String newRight) {
		str = str.replaceAll("\\>\\)", ">>))");
		while (str.indexOf(">>))") >= 0) {
			rgNum++;
			str = str.replaceFirst("\\>\\>\\)\\)", ">:rg" + rgNum + ")");
		}
		return str;
	}

}
