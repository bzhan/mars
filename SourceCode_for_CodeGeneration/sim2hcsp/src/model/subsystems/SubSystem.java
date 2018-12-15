package model.subsystems;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;
import model.SL_Diagram;
import model.Utilize;

public class SubSystem extends SL_Block {

	private SL_Diagram subDiagram;
	private boolean broken;
	private String process;

	// for enabled semantics
	private HashMap<String, String> semantics;

	public SubSystem(String blockType, String blockName, Node node,
			String diagLocation) {
		super(blockType, blockName);
		parameters.put("st", "-1");
		subDiagram = new SL_Diagram(node, diagLocation + blockName + "_");

		if (subDiagram.isBroken()) {
			broken = true;
		} else {
			broken = false;
		}
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		return semantics;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		return semantics;
	}

	public String getSystemType() {

		int i = 0;
		for (SL_Block b : subDiagram.getBlocks().values()) {
			if (b.getType().equals("TriggerPort")) {
				i += 2;
			} else if (b.getType().equals("EnablePort")) {
				i += 3;
			}
		}

		if (i == 0)
			return "Normal";
		if (i == 2)
			return "Trigger";
		else if (i == 3)
			return "Enable";
		else
			return "complex";
	}

	public SL_Diagram getSubDiagram() {
		return subDiagram;
	}

	public String getProcess() {
		return process;
	}

	public void setSemantics(HashMap<String, String> semantics) {
		this.semantics = semantics;
	}

	public void setProcess(String process) {
		this.process = process;
	}

	public boolean isBroken() {
		return broken;
	}

	// for print
	public void printBlock(int level) {
		String head = Utilize.tabsAhead(level);
		super.printBlock(level);
		System.out.println(head + "\tsubdiagram:");
		subDiagram.printDiagram(level + 1);
	}

}
