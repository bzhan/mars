package model.mathOperations;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Gain extends SL_Block {

	public Gain(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("k", "1");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Gain")) {
				parameters.put("k", n.getFirstChild().getNodeValue());
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
		String K = "(Real " + super.getParameters().get("k").replaceAll("-", "--") + ")";

		ret.put("init", "");
		ret.put("0", Out1 + "=" + K + "*" + In1);
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String K = "(Real " + super.getParameters().get("k").replaceAll("-", "--") + ")";
		ret.put("fun", Out1 + ":=(" + K + "*" + In1 + ")");
		return ret;
	}

}
