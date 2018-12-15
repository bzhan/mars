package model.stateflow;

import java.util.ArrayList;

import m2h.Isabelle;
import m2h.SL2HCSP;

public class SFIsabelle {
	static int assNum = 0;
	static ArrayList<String> processNames = new ArrayList<String>();

	public static void isabelle(Stateflow sf) {
		// variable definitions
		String varStr = "";
		if (assNum == 0)
			varStr = Isabelle.head(sf.getName() + "VarDef", "assertionDef");
		else
			varStr = Isabelle.head(sf.getName() + "VarDef",
					SFProcess.sfName.get(SFProcess.sfNum) + "PDef");
		varStr += SFIsabelle.channelDef(sf);
		varStr += SFIsabelle.eventDefAssist(sf);
		varStr += SFIsabelle.eventDef(sf);
		varStr += SFIsabelle.varDef(sf);
		varStr += Isabelle.end();
		Isabelle.isabelleWrite(sf.getName() + "VarDef.thy", varStr);

		// process definitions
		String processStr = Isabelle.head(sf.getName() + "PDef", sf.getName()
				+ "ADef");
		processStr += SFIsabelle.getPAssist(sf);
		processStr += sf.processAss;
		processStr += SFIsabelle.getProcesses(sf);
		processStr = processStr.replaceAll("\\(\\)", "");
		processStr += Isabelle.end();
		Isabelle.isabelleWrite(sf.getName() + "PDef.thy", processStr);

		// assertion definitions
		String assertionStr = Isabelle.head(sf.getName() + "ADef", sf.getName()
				+ "VarDef");
		assertionStr += SFIsabelle.assertionDef();
		assertionStr += Isabelle.end();
		if (SL2HCSP.rewriteAss || SL2HCSP.rewriteAll)
			Isabelle.isabelleWrite(sf.getName() + "ADef.thy", assertionStr);

		if (SL2HCSP.isTextPrint()) {
			SFProcess.printTProcess(sf);
		}
	}

	// define channel names
	protected static String channelDef(Stateflow sf) {
		int n = SFProcess.getSize(sf);
		String def = "(*Define channel names.*)\n";
		for (int i = 1; i <= n; i++) {
			def += "definition BC_" + i + " :: cname where\n" + "\"BC_" + i
					+ " == \'\'BC_" + i + "\'\'\"\n";
			def += "definition BR_" + i + " :: cname where\n" + "\"BR_" + i
					+ " == \'\'BR_" + i + "\'\'\"\n";
			def += "definition BO_" + i + " :: cname where\n" + "\"BO_" + i
					+ " == \'\'BO_" + i + "\'\'\"\n";
			def += "definition VO" + i + " :: cname where\n" + "\"VO" + i
					+ " == \'\'VO" + i + "\'\'\"\n";
			def += "definition VI" + i + " :: cname where\n" + "\"VI" + i
					+ " == \'\'VI" + i + "\'\'\"\n";
			def += "definition vBO" + i + " :: exp where\n" + "\"vBO" + i
					+ " == SVar \'\'vBO" + i + "\'\'\"\n";
		}
		if (!sf.getParameters().get("st").equals("-1")) {
			String chTri = "Ch_" + sf.getName() + "_1";
			def += "definition " + chTri + " :: cname where\n" + "\"" + chTri
					+ " == \'\'" + chTri + "\'\'\"\n";
		}
		return def + "\n";
	}

	protected static String eventDefAssist(Stateflow sf) {
		String def = "(*Define event variables assistent.*)\n";
		def += "consts eL :: \"exp list\"\n";
		def += "consts nL :: \"exp list\"\n";
		return def;
	}

	// define event variable names
	protected static String eventDef(Stateflow sf) {
		int n = SFProcess.getSize(sf);
		String def = "(*Define event variables.*)\n";
		for (int i = 1; i <= n; i++) {
			def += "definition E" + i + " :: exp where\n" + "\"E" + i
					+ " == SVar \'\'E" + i + "\'\'\"\n";
			def += "definition done" + i + " :: exp where\n" + "\"done" + i
					+ " == RVar \'\'done" + i + "\'\'\"\n";
		}
		def += "definition E :: exp where\n\"E == SVar \'\'E\'\'\"\n";
		def += "definition num :: exp where\n\"num == RVar \'\'num\'\'\"\n";
		def += "definition EL :: exp where\n\"EL == List eL\"\n";
		def += "definition NL :: exp where\n\"NL == List nL\"\n";
		return def;
	}

	// define local and sending variables and events
	protected static String varDef(Stateflow sf) {
		String def = "(*Define local and sending variables.*)\n";
		// // clock
		// def += "definition Ch_" + sf.getName() + "_Tri1" +
		// " :: cname where\n"
		// + "\"Ch_" + sf.getName() + "_Tri" + (SFProcess.sfNum + 1)
		// + " == \'\'Ch_" + sf.getName() + "_Tri" + (SFProcess.sfNum + 1)
		// + "\'\'\"\n";
		// trigger channel
		def += "definition sfTemp" + (SFProcess.sfNum + 1) + " :: exp where\n"
				+ "\"sfTemp" + (SFProcess.sfNum + 1) + " == RVar \'\'sfTemp"
				+ (SFProcess.sfNum + 1) + "\'\'\"\n";
		// def += "definition T :: \"exp\" where" + "\"T == (RVar ''T'')\"\n";
		def += diagVarDef(sf.getDiagram());
		for (SF_Junction loc : sf.getLocations().values()) {
			if (!loc.isState())
				continue;
			if (((SF_State) loc).getDiagram() == null
					|| ((SF_State) loc).getDiagram().getCompositeType() == null)
				continue;
			def += diagVarDef(((SF_State) loc).getDiagram());
		}
		// active or not for every state
		for (SF_Junction loc : sf.getLocations().values()) {
			if (loc.isState()) {
				def += "definition act" + loc.getName() + " :: exp where\n"
						+ "\"act" + loc.getName() + " == RVar \'\'act"
						+ loc.getName() + "\'\'\"\n";
			}
		}
		// defined shared variables
		int n = SFProcess.getSize(sf);
		// input variables
		def += "(*Define input variables.*)\n";
		ArrayList<String> iVars = sf.getDiagram().getIvars();
		for (String var : iVars) {
			for (int i = 1; i <= n; i++) {
				def += "definition " + var + i + " :: exp where\n" + "\"" + var
						+ i + " == RVar \'\'" + var + i + "\'\'\"\n";
			}
		}
		// output variables
		def += "(*Define output variables.*)\n";
		ArrayList<String> oVars = sf.getDiagram().getOvars();
		for (String var : oVars) {
			for (int i = 1; i <= n; i++) {
				def += "definition " + var + i + " :: exp where\n" + "\"" + var
						+ i + " == RVar \'\'" + var + i + "\'\'\"\n";
			}
		}
		// local variables
		def += "(*Define local variables.*)\n";
		ArrayList<String> lVars = sf.getDiagram().getLvars();
		for (String var : lVars) {
			for (int i = 1; i <= n; i++) {
				def += "definition " + var + i + " :: exp where\n" + "\"" + var
						+ i + " == RVar \'\'" + var + i + "\'\'\"\n";
			}
		}

		def += "\n";
		return def;
	}

	// define variables used in a diagram
	protected static String diagVarDef(SF_Diagram diagram) {
		String def = "";
		// constant
		for (String c : diagram.getcNames()) {
			def += "definition " + c + " :: exp where\n" + "\"" + c
					+ " == RVar \'\'" + c + "\'\'\"\n";
		}
		// local variables
		for (String lvar : diagram.getLvars()) {
			def += "definition " + lvar + " :: exp where\n" + "\"" + lvar
					+ " == RVar \'\'" + lvar + "\'\'\"\n";
		}
		// input variables
		for (String ivar : diagram.getIvars()) {
			def += "definition " + ivar + " :: exp where\n" + "\"" + ivar
					+ " == RVar \'\'" + ivar + "\'\'\"\n";
		}
		// output variables
		for (String ovar : diagram.getOvars()) {
			def += "definition " + ovar + " :: exp where\n" + "\"" + ovar
					+ " == RVar \'\'" + ovar + "\'\'\"\n";
		}
		// local events
		for (String lE : diagram.getLEvents()) {
			def += "definition " + lE + " :: exp where\n" + "\"" + lE
					+ " == RVar \'\'" + lE + "\'\'\"\n";
		}
		// input events
		for (String iE : diagram.getIEvents()) {
			def += "definition " + iE + " :: exp where\n" + "\"" + iE
					+ " == RVar \'\'" + iE + "\'\'\"\n";
		}
		// output events
		for (String oE : diagram.getOEvents()) {
			def += "definition " + oE + " :: exp where\n" + "\"" + oE
					+ " == RVar \'\'" + oE + "\'\'\"\n";
		}
		return def;
	}

	// definition version
	protected static String assertionDef() {
		String assertion = "";
		for (int i = 1; i <= assNum; i++) {
			assertion += "definition assSF" + i + " :: mid where\n" + "\"";
			assertion += "assSF" + i + " == (WTrue,l[=](Real 0))" + "\"\n";
		}
		assertion += "\n";

		return assertion;
	}

	private static String getPAssist(Stateflow sf) {
		// define functions
		String process = "(*Define the processes for fuctions.*)\n";
		process += "definition min :: \"exp => exp => exp\" where"
				+ "\"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)\"\n";

		int i = 1;
		int start = 1;
		for (SF_Junction location : sf.getLocations().values()) {
			if (location.getSSID().startsWith("F")) {
				SF_Function f = ((SF_Function) location);
				String fun = f.getFun().substring(9 + f.getName().length());
				fun = fun.replaceAll("\\(\\)", "");
				fun = SFProcess.fun2HCSP(fun);
				fun = SFProcess.delTail(fun);
				while (fun.length() > 80 && fun.indexOf(";", 80) > 0) {
					String sub = fun.substring(0, fun.indexOf(";", 80));
					sub = appearTimesCal(sub, ";");
					process += "definition F" + sf.getName() + i
							+ " :: proc where\n" + "\"F" + sf.getName() + i
							+ " == " + sub + "\"\n";
					i++;
					fun = fun.substring(fun.indexOf(";", 80) + 1);
				}
				fun = appearTimesCal(fun, ";");
				process += "definition F" + sf.getName() + i
						+ " :: proc where\n" + "\"F" + sf.getName() + i
						+ " == " + fun + "\"\n";
				i++;
				// total
				String total = "";
				for (int j = start; j < i; j++) {
					total += "F" + sf.getName() + j + ";";
				}
				total = SFProcess.delTail(total);
				total = appearTimesCal(total, ";");
				process += "definition " + f.getName() + " :: proc where\n"
						+ "\"" + f.getName() + " == " + total + "\"\n";
				start = i;

				// process += "consts " + f.getName() + " :: proc\n";
				// System.out.println(fun);
			}
		}
		return process;
	}

	// define processes
	public static String getProcesses(Stateflow sf) {

		ArrayList<String> monitor = SFProcess.getMonitor(sf);
		ArrayList<String> main = SFProcess.getMainProcess(sf);
		String process = "(*Define the process.*)\n";

		int i = 1;
		for (String str : monitor) {
			str = appearTimesCal(str, ";");
			process += "definition P" + sf.getName() + i + " :: proc where\n"
					+ "\"P" + sf.getName() + i + " == " + str + "\"\n";
			i++;
		}

		for (String str : main) {
			str = appearTimesCal(str, ";");
			process += "definition P" + sf.getName() + i + " :: proc where\n"
					+ "\"P" + sf.getName() + i + " == " + str + "\"\n";
			i++;
		}

		// define the whole process
		process += "definition P" + sf.getName() + " :: proc where\n" + "\"P"
				+ sf.getName() + " == " + processNames.get(0);
		for (int j = 1; j < processNames.size(); j++) {
			process += "||" + processNames.get(j);
		}
		process += "\"\n";

		return process;
	}

	private static String appearTimesCal(String process, String string) {
		String result = "";
		for (int i = 0; i < process.length(); i++) {
			if (process.substring(i, i + 1).equals(string)) {
				result += ";assSF" + (++assNum) + ";";
			} else {
				result += process.substring(i, i + 1);
			}
		}
		return result;
	}

}
