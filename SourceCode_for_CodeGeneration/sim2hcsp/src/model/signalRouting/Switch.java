package model.signalRouting;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Switch extends SL_Block {

	public Switch(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("op", ">=");
		parameters.put("th", "0");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Criteria")) {
				if (n.getFirstChild().getNodeValue().contains(">=")) {
					parameters.put("op", ">=");
				} else if (n.getFirstChild().getNodeValue().contains("~=")) {
					parameters.put("op", "~=");
				} else {
					parameters.put("op", ">");
				}
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Threshold")) {
				parameters.put("th", n.getFirstChild().getNodeValue());
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
		String In3 = super.getinVarNames().get(3);
		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");
		String th = "(Real " + super.getParameters().get("th") + ")";

		String b1 = "";
		String b2 = "";
		if (op.replaceAll(" ", "").equals("~=")) {
			b1 = In2 + "==False";
			b2 = In2 + "==True";
		} else {
			b1 = "~(" + In2 + op + th + ")";
			b2 = In2 + op + th;
		}

		ret.put("init", "");
		ret.put("0", Out1 + "==" + In3);
		ret.put("0b", b1);
		ret.put("1", Out1 + "==" + In1);
		ret.put("1b", b2);
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();
		String In1 = super.getinVarNames().get(1);
		String In2 = super.getinVarNames().get(2);
		String In3 = super.getinVarNames().get(3);
		String Out1 = super.getName() + "_1";
		String op = super.getParameters().get("op");
		String th = "(Real " + super.getParameters().get("th") + ")";

		String b1 = "";
		String b2 = "";
		if (op.replaceAll(" ", "").equals("~=")) {
			b1 = In2 + "==False";
			b2 = In2 + "==True";
		} else {
			b1 = "!(" + In2 + op + th + ")";
			b2 = "(" + In2 + op + th + ")";
		}

		String ret1 = "IF (" + b1 + ") (" + Out1 + ":=" + In3 + ")";
		String ret2 = "IF (" + b2 + ") (" + Out1 + ":=" + In1 + ")";
		ret.put("fun", ret1 + "; " + ret2);
		return ret;
	}

}
