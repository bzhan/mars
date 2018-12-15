package model.continuous;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Integrator extends SL_Block {

	public Integrator(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("init", "0");
		parameters.put("st", "0");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("InitialCondition")) {
				parameters.put("init", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();
		ret.put("init", this.getName() + "_1" + ":=(Real " + parameters.get("init") + ")");
		ret.put("0", "diff(" + this.getName() + "_1" + ")==" + super.getinVarNames().get(1));
		ret.put("0b", "");

		return ret;
	}

}
