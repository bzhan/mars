package model.mathOperations;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class MinMax extends SL_Block {

	public MinMax(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("op", "min");
		parameters.put("num", "1");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Function")) {
				parameters.put("op", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Inputs")) {
				parameters.put("num", n.getFirstChild().getNodeValue());
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
		String In2 = super.getinVarNames().get(2);
		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");

		ret.put("init", "");
		ret.put("0", Out1 + "=" + op + "(" + In1 + In2 + ")");
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String In2 = super.getinVarNames().get(2);
		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");
		ret.put("fun", Out1 + "=" + op + "(" + In1 + In2 + ")");
		return ret;
	}

}
