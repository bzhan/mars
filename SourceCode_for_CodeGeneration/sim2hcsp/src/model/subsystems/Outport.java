package model.subsystems;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Outport extends SL_Block {
	private String diagLocation;

	public Outport(String blockType, String blockName, Node node, String diagStr) {
		super(blockType, blockName);
		this.diagLocation = diagStr;

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("st", "0");
		parameters.put("Port", "1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("Port")) {
				parameters.put("Port", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = diagLocation + this.parameters.get("Port");

		String retStr = Out1 + "=" + In1;
		ret.put("fun", retStr);
		return ret;
	}

	public void setSubsystemName(String subsystemName) {
		this.diagLocation = subsystemName;
	}

}
