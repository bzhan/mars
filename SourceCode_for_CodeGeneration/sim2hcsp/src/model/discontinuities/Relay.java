package model.discontinuities;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Relay extends SL_Block {

	public Relay(String blockType, String blockName, Node node) {
		super(blockType, blockName);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("onpoint", "eps");
		parameters.put("offpoint", "eps");
		parameters.put("onval", "1");
		parameters.put("offval", "0");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("OnSwitchValue")) {
				parameters.put("onpoint", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("OffSwitchValue")) {
				parameters.put("offpoint", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("OnOutputValue")) {
				parameters.put("onval", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("OffOutputValue")) {
				parameters.put("offval", n.getFirstChild().getNodeValue());
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
		String onpoint = "(Real " + super.getParameters().get("onpoint") + ")";
		String offpoint = "(Real " + super.getParameters().get("offpoint") + ")";
		String onval = "(Real " + super.getParameters().get("onval") + ")";
		String offval = "(Real " + super.getParameters().get("offval") + ")";

		ret.put("init", "");
		ret.put("0", Out1 + "=" + offval);
		ret.put("0b", In1 + "<" + onpoint);
		ret.put("1", Out1 + "=" + onval);
		ret.put("1b", In1 + ">" + offpoint);
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String onpoint = "(Real " + super.getParameters().get("onpoint") + ")";
		String offpoint = "(Real " + super.getParameters().get("offpoint") + ")";
		String onval = "(Real " + super.getParameters().get("onval") + ")";
		String offval = "(Real " + super.getParameters().get("offval") + ")";

		String ret1 = "(" + In1 + "<" + onpoint + ") -> " + Out1 + ":=" + offval;
		String ret2 = "(" + In1 + ">" + offpoint + ") -> " + Out1 + ":=" + onval;
		ret.put("fun", ret1 + "; " + ret2);
		return ret;
	}

}
