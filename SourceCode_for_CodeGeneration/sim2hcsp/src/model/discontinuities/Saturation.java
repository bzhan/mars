package model.discontinuities;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Saturation extends SL_Block {

	public Saturation(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("max", "0.5");
		parameters.put("min", "-0.5");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("UpperLimit")) {
				parameters.put("max", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("LowerLimit")) {
				parameters.put("min", n.getFirstChild().getNodeValue());
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
		String min = "(Real " + super.getParameters().get("min") + ")";
		String max = "(Real " + super.getParameters().get("max") + ")";

		ret.put("init", "");
		ret.put("0", Out1 + "=" + In1);
		ret.put("0b", min + "<=" + In1 + "<=" + max);
		ret.put("1", Out1 + "=" + max);
		ret.put("1b", In1 + ">" + max);
		ret.put("2", Out1 + "=" + min);
		ret.put("2b", In1 + "<" + min);
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String min = "(Real " + super.getParameters().get("min") + ")";
		String max = "(Real " + super.getParameters().get("max") + ")";

		String ret1 = "IF (" + min + "<=" + In1 + " & " + In1 + "<=" + max + ") " + Out1 + ":=" + In1;
		String ret2 = "IF (" + In1 + ">" + max + ") " + Out1 + ":=" + max;
		String ret3 = "IF (" + In1 + "<" + min + ") " + Out1 + ":=" + min;
		
		ret.put("fun", ret1 + "; " + ret2 + "; " + ret3);
		return ret;
	}

}
