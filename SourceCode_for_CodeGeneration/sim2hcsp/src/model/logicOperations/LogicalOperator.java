package model.logicOperations;

import java.util.ArrayList;
import java.util.HashMap;

import model.SL_Block;

import org.w3c.dom.Node;

public class LogicalOperator extends SL_Block {

	public LogicalOperator(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("op", "AND");
		parameters.put("num", "2");
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Operator")) {
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

		String op = super.getParameters().get("op");
		String In = "(" + super.getinVarNames().get(1);
		for (int i = 2; i <= super.getinVarNames().values().size(); i++) {
			In += op + super.getinVarNames().get(i);
		}
		In += ") ";

		String Out1 = super.getName() + "_1";

		ret.put("init", "");
		ret.put("0", Out1 + "=" + In.replaceAll("AND", "&").replaceAll("OR", "|"));
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String op = super.getParameters().get("op");
		String In = "(" + super.getinVarNames().get(1) + "==True";
		for (int i = 2; i <= super.getinVarNames().values().size(); i++) {
			In += op + super.getinVarNames().get(i) + "==True";
		}
		In += ") ";

		String Out1 = super.getName() + "_1";

		String ret1 = "IF " + In + Out1 + ":=True";
		String ret2 = "IF (~" + In + ") " + Out1 + ":=False";
		String retStr = ret1 + "; "  + ret2;
		retStr = retStr.replaceAll("AND", "&");
		retStr = retStr.replaceAll("OR", "|");
		ret.put("fun", retStr);
		return ret;
	}

}
