package model.sources;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Clock extends SL_Block {

	public Clock(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("st", "0");
		parameters.put("deci", "0");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Decimation")) {
				parameters.put("deci", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();
		String Out1 = super.getName() + "_1";
		String deci = "(Real " + super.getParameters().get("deci") + ")";
		ret.put("init", Out1 + ":=0");
		ret.put("fun", Out1 + ":=" + Out1 + "+" + deci + "*T");
		return ret;
	}

}
