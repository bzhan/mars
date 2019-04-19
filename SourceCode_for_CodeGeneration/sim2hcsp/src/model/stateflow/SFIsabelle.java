package model.stateflow;

import java.util.ArrayList;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

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
		else {
			System.out.println(assNum);
			System.out.println(SFProcess.sfName);
			System.out.println(SFProcess.sfNum);
			varStr = Isabelle.head(sf.getName() + "VarDef", SFProcess.sfName.get(SFProcess.sfNum - 1) + "PDef");
		}
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
		processStr = addSKIP(processStr); // patch
		Isabelle.isabelleWrite(sf.getName() + "PDef.thy", processStr);

		// sf.getName()+PDef.thy -> sf.getName()+.hcsp
		Isabelle.isabelleWrite(sf.getName()+".hcsp", getHCSP(processStr));

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

	public static String addSKIP(String processStr){
		StringBuilder processStr_builder = new StringBuilder(processStr);
		String pattern = "assSF\\d*;[) ]*;assSF\\d*";
		Pattern p = Pattern.compile(pattern);
		Matcher m = p.matcher(processStr);
		while(m.find()){
			int start = m.start();
			int end = m.end();
			String str = processStr.substring(start, end);
			if(str.contains(";)"))
				str = str.replaceAll(";\\)", ";Skip)");
			else
				str = str.replaceAll(";;", ";Skip;");
			processStr_builder.replace(start, end, str);
			processStr = processStr_builder.toString();
			m = p.matcher(processStr);
		}
		return processStr;
	}

	public static String getHCSP(String processStr){
		String hcspStr = "";
		hcspStr = processStr.replaceAll("assSF\\d+;", "");
		hcspStr = hcspStr.replaceAll(":=", "=");
		hcspStr = hcspStr.replaceAll("==", "::=");
		hcspStr = hcspStr.replaceAll("\\[\\+\\]", "+");
		hcspStr = hcspStr.replaceAll("\\[-\\]", "-");
		hcspStr = hcspStr.replaceAll("\\[\\*\\]", "*");
		hcspStr = hcspStr.replaceAll("\\[/\\]", "/");
		hcspStr = hcspStr.replaceAll("\\[<\\]", "<");
		hcspStr = hcspStr.replaceAll("\\[>\\]", ">");
		hcspStr = hcspStr.replaceAll("\\[<=\\]", "<=");
		hcspStr = hcspStr.replaceAll("\\[>=\\]", ">=");
		hcspStr = hcspStr.replaceAll("\\[=\\]", "==");
		hcspStr = hcspStr.replaceAll("\\[~\\]", "~");
		hcspStr = hcspStr.replaceAll("\\[&\\]", "&&");
		// (Real number) -> number
		StringBuilder hcspStr_builder = new StringBuilder(hcspStr);
		Pattern p = Pattern.compile("\\(Real[^)]*\\)");
		Matcher m = p.matcher(hcspStr);
		while (m.find()){
			int start = m.start();
			int end = m.end();
			String number = hcspStr.substring(start+6, end-1);
			hcspStr_builder.replace(start, end, number);
			hcspStr = hcspStr_builder.toString();
			m = p.matcher(hcspStr);
		}
		//IF (Condition) (Actions) -> if (Condition) then Actions else Skip;
		hcspStr_builder = new StringBuilder(hcspStr);
		p = Pattern.compile("IF.*?\\(");
		m = p.matcher(hcspStr);
		while (m.find()){
			int start = m.start();
			int end = m.end();
			hcspStr_builder.replace(start, start+2, "if"); // IF -> if
			hcspStr = hcspStr_builder.toString();
			// Find the condition
			int left_parenthesis = 1;
			int index = end;
			while (left_parenthesis > 0){
				if (hcspStr.charAt(index) == '(')
					left_parenthesis++;
				else if (hcspStr.charAt(index) == ')')
					left_parenthesis--;
				index++;
			}
			String condition = hcspStr.substring(end-1, index);
			// Find the action
			while (hcspStr.charAt(index) != '(')
				index++;
			start = index;
			left_parenthesis = 1;
			while (left_parenthesis > 0){
				index++;
				if (hcspStr.charAt(index) == '(')
					left_parenthesis++;
				else if (hcspStr.charAt(index) == ')')
					left_parenthesis--;
			}
			String action = hcspStr.substring(start, index+1);
			// IF (...) (...) -> if (...) then (...) else Skip
			hcspStr_builder.replace(end-1, index+1, condition+" then "+action+" else Skip");
			hcspStr = hcspStr_builder.toString();
			m = p.matcher(hcspStr);
		}

		return hcspStr;
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
		def += "definition SE :: exp where\n\"SE == SVar \'\'E\'\'\"\n";
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
