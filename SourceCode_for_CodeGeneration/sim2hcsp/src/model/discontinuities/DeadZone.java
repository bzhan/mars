package model.discontinuities;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class DeadZone extends SL_Block {

	public DeadZone(String blockType, String blockName, Node node) {
		super(blockType, blockName);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("LL", "-0.5");
		parameters.put("UL", "0.5");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("LowerValue")) {
				parameters.put("LL", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("UpperValue")) {
				parameters.put("UL", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("SampleTime")) {
				parameters.put("st", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String LL = "(Real " + super.getParameters().get("LL") + ")";
		String UL = "(Real " + super.getParameters().get("UL") + ")";

		ret.put("init", "");
		ret.put("0", Out1 + "=0");
		ret.put("0b", LL + "<=" + In1 + "<=" + UL);
		ret.put("1", Out1 + "=" + In1 + "-" + UL);
		ret.put("1b", In1 + ">" + UL);
		ret.put("2", Out1 + "=" + In1 + "-" + LL);
		ret.put("2b", In1 + "<" + LL);
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String LL = "(Real " + super.getParameters().get("LL") + ")";
		String UL = "(Real " + super.getParameters().get("UL") + ")";

		String ret1 = "(" + LL + "<=" + In1 + "<=" + UL + ") -> " + Out1 + ":=0";
		String ret2 = "(" + In1 + ">" + UL + ") -> " + Out1 + ":=" + In1 + "-" + UL;
		String ret3 = "(" + In1 + "<" + LL + ") -> " + Out1 + ":=" + In1 + "-" + LL;

		ret.put("fun", ret1 + "; " + ret2 + "; " + ret3);
		return ret;
	}

}
