package model.discrete;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class ZeroOrderHold extends SL_Block {

	public ZeroOrderHold(String blockType, String blockName, Node node) {
		super(blockType, blockName);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("st", "1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
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
		ret.put("fun", Out1 + ":=" + In1);
		return ret;
	}

}
