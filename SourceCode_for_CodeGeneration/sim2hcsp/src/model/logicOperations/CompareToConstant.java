package model.logicOperations;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class CompareToConstant extends SL_Block {

	public CompareToConstant(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("c", "0");
		parameters.put("st", "0");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("relop")) {
				parameters.put("op", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("const")) {
				parameters.put("c", n.getFirstChild().getNodeValue());
			}
		}

		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");
		String c = "(Real " + super.getParameters().get("c") + ")";

		ret.put("init", "");
//		ret.put("0", Out1 + "=1");
//		ret.put("0b", In1 + op + c);
//		ret.put("1", Out1 + "=0");
//		ret.put("1b", "~(" + In1 + op + c + ")");
		ret.put("0", Out1 + "=(" + In1 + op + c + ")");
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");
		String c = "(Real " + super.getParameters().get("c") + ")";

		String ret1 = "(" + In1 + op + c + ") -> " + Out1 + ":=1";
		String ret2 = "(" + "~(" + In1 + op + c + ")" + ") -> " + Out1 + ":=0";
		ret.put("fun", ret1 + "; " + ret2);
		return ret;
	}

}
