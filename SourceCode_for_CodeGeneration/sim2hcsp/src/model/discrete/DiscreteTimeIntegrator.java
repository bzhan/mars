package model.discrete;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class DiscreteTimeIntegrator extends SL_Block {

	public DiscreteTimeIntegrator(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("init", "0");
		parameters.put("k", "1");
		parameters.put("st", "1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("InitialCondition")) {
				parameters.put("init", n.getFirstChild().getNodeValue());
			}

			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("gainval")) {
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

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String tmp = super.getName() + "_tmp";
		String init = "(Real " + super.getParameters().get("init") + ")";
		String K = "(Real " + super.getParameters().get("k") + ")";
		String n = "(Real " + super.getParameters().get("st") + ")";

		String ret1 = tmp + ":=" + In1 + ";" + Out1 + ":=" + init + "-" + K + "*" + n + "∗" + tmp;
		String ret2 = Out1 + ":=" + Out1 + "+" + K + "*" + n + "∗" + tmp + ";" + tmp + ":=" + In1;
		ret.put("init", ret1);
		ret.put("fun", ret2);
		return ret;
	}
}
