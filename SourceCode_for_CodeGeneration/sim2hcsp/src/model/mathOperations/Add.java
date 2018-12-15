package model.mathOperations;

import java.util.ArrayList;
import java.util.HashMap;

import model.SL_Block;

import org.w3c.dom.Node;

public class Add extends SL_Block {

	public Add(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("op", "++");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("Inputs")) {
				parameters.put("op", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("SampleTime")) {
				parameters.put("st", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");

		String str = "";
		if (op.startsWith("+") || op.startsWith("-")) {
			str = "(Real 0)";
			for (int i = 1; i <= op.length(); i++) {
				str = str + String.valueOf(parameters.get("op").charAt(i - 1))
						+ getinVarNames().get(i);
			}
		} else {
			str = getinVarNames().get(1);
			for (int i = 2; i <= Integer.parseInt(op); i++) {
				str = str + "+" + getinVarNames().get(i);
			}
		}

		ret.put("init", "");
		ret.put("0", Out1 + "=" + str);
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");

		String str = "";
		if (op.startsWith("+") || op.startsWith("-")) {
			str = "(Real 0)";
			for (int i = 1; i <= op.length(); i++) {
				str = str + String.valueOf(parameters.get("op").charAt(i - 1))
						+ getinVarNames().get(i);
			}
		} else {
			str = getinVarNames().get(1);
			for (int i = 2; i <= Integer.parseInt(op); i++) {
				str = str + "+" + getinVarNames().get(i);
			}
		}

		ret.put("fun", Out1 + ":=(" + str+")");
		return ret;
	}

}
