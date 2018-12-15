package model.discrete;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

public class UnitDelay extends Memory {

	public UnitDelay(String blockType, String blockName, Node node) {
		super(blockType, blockName, node);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("init", "0");
		parameters.put("st", "-1");
		parameters.put("discrete", "");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("X0")) {
				parameters.put("init", n.getFirstChild().getNodeValue());
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

		String ret1 = tmp + ":=" + init;
		String ret2 = Out1 + ":=" + tmp + ";" + tmp + ":=" + In1;
		ret.put("init", ret1);
		ret.put("fun", ret2);
		return ret;
	}

}
