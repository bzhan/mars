package model.sources;

import java.util.ArrayList;
import java.util.HashMap;

import model.SL_Block;

import org.w3c.dom.Node;

public class Constant extends SL_Block {

	public Constant(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("val", "1");
		parameters.put("st", "inf");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Value")) {
				parameters.put("val", n.getFirstChild().getNodeValue());
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
//		ret.put("init",
//				this.getName() + "_1" + ":=(Real " + parameters.get("val").replaceAll("-", "--")
//						+ ")");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();
//		ret.put("init",
//				this.getName() + "_1" + ":=(Real " + parameters.get("val").replaceAll("-", "--")
//						+ ")");
		return ret;
	}

}
