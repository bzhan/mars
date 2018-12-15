package model;

import java.util.ArrayList;
import java.util.HashMap;

import m2h.Comms;
import m2h.SL2HCSP;

public class SL_Block {

	private String type;
	private String name;
	private ArrayList<Boolean> outTypes;
	private HashMap<Integer, ArrayList<SL_Line>> srcLines = new HashMap<Integer, ArrayList<SL_Line>>();
	private HashMap<Integer, SL_Line> dstLines = new HashMap<Integer, SL_Line>();
	protected HashMap<String, String> parameters = new HashMap<String, String>();

	public SL_Block(String blockType, String blockName) {
		this.type = blockType;
		this.name = blockName;
		this.getParameters().put("st", "0");
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		System.out.println("Wrong using of semantics function!");
		return parameters;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		System.out.println("Wrong using of semantics function!");
		return parameters;
	}

	public void addLine(SL_Line line, int port) {
		if (line == null) {
			throw new IllegalArgumentException();
		}

		if (line.getTarget() == this) { // inlines
			dstLines.put(port, line);
		} else if (line.getSource() == this) { // outlines
			if (srcLines.containsKey(port)) {
				srcLines.get(port).add(line);
			} else {
				ArrayList<SL_Line> ls = new ArrayList<SL_Line>();
				ls.add(line);
				srcLines.put(port, ls);
			}
		}
	}

	public void removeLine(SL_Line line) {
		if (line == null) {
			throw new IllegalArgumentException();
		}
		if (line.getTarget() == this) {
			dstLines.remove(line.getDstPort());
		} else if (line.getSource() == this) {
			srcLines.get(line.getSrcPort()).remove(line.getBranch());
			if (srcLines.get(line.getSrcPort()).isEmpty())
				srcLines.remove(line.getSrcPort());
			else {
				// repair the branches
				for (int i = 0; i < srcLines.get(line.getSrcPort()).size(); i++) {
					srcLines.get(line.getSrcPort()).get(i).setBranch(i);
				}
			}
		}
	}

	public String getType() {
		return type;
	}

	public String getName() {
		return name;
	}

	// change the block name to keep the structure when delete a subsystem
	public void setName(String str) {
		name = str;
	}

	public HashMap<Integer, SL_Line> getDstLines() {
		return dstLines;
	}

	public HashMap<Integer, ArrayList<SL_Line>> getSrcLines() {
		return srcLines;
	}

	public SL_Line getDstLine(int i) {
		if (dstLines.containsKey(i))
			return dstLines.get(i);
		else
			return null;
	}

	public ArrayList<SL_Line> getSrcLine(int i) {
		if (srcLines.containsKey(i))
			return srcLines.get(i);
		else
			return null;
	}

	public HashMap<String, String> getParameters() {
		return parameters;
	}

	public void setParameters(HashMap<String, String> parameters) {
		this.parameters = parameters;
	}

	// for semantics of blocks
	public HashMap<Integer, String> getinVarNames() {
		HashMap<Integer, String> ret = new HashMap<Integer, String>();

		for (SL_Line l : dstLines.values()) {
			ret.put(l.getDstPort(), l.getVarName());
		}
		return ret;
	}

	public ArrayList<Boolean> getOutTypes() {
		return outTypes;
	}

	protected void setOutTypes(ArrayList<Boolean> outTypes) {
		this.outTypes = outTypes;
	}

	// for print
	public void printBlock(int level) {
		String head = Utilize.tabsAhead(level);
		System.out.println(head + "type:\t" + type);
		System.out.println(head + "name:\t" + name);
		for (String s : parameters.keySet()) {
			System.out.println(head + "ps:" + "\t" + s + "\t" + parameters.get(s));
		}
		if (parameters.isEmpty()) {
			System.out.println(head + "ps:" + "\t" + "null");
		}
	}

	public void printLines(int level) {
		String head = Utilize.tabsAhead(level);
		if (dstLines.isEmpty())
			System.out.println(head + "Ins:\t" + "null");
		else
			System.out.print(head + "Ins:");
		for (SL_Line l : dstLines.values()) {
			if (!SL2HCSP.isCommLinesPrint() && Comms.isCommLine(l))
				continue;
			else
				l.printLine(level);
		}

		if (srcLines.isEmpty())
			System.out.println(head + "Outs:\t" + "null");
		else
			System.out.print(head + "Outs:");
		for (ArrayList<SL_Line> ls : srcLines.values()) {
			for (SL_Line l : ls)
				if (!SL2HCSP.isCommLinesPrint() && Comms.isCommLine(l))
					continue;
				else
					l.printLine(level);
		}
		System.out.println();
	}

}
