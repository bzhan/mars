package model.sinks;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Display extends SL_Block {

	public Display(String blockType, String blockName, Node node) {
		super(blockType, blockName);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("st", "0");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null && n.getAttributes().getNamedItem("Name").getNodeValue().equals("Decimation")) {
				parameters.put("deci", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		ret.put("init", "");
		ret.put("0", "Stop");
		ret.put("0b", "");
		return ret;
//		String In1 = super.getinVarNames().get(1);
//		String Out1 = super.getName() + "_1";
//
//		ret.put("init", "");
//		ret.put("0", Out1 + "=" + In1);
//		ret.put("0b", "");
//		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		ret.put("fun", "Skip");
		return ret;
//		String In1 = super.getinVarNames().get(1);
//		String Out1 = super.getName() + "_1";
//		ret.put("fun", Out1 + ":=" + In1);
//		return ret;
	}

}
