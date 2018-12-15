package model.discontinuities;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class HitCrossing extends SL_Block {

	public HitCrossing(String blockType, String blockName, Node node) {
		super(blockType, blockName);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("offset","0");
		parameters.put("st","-1");

		
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("HitCrossingOffset")) {
				parameters.put("offset", n.getFirstChild().getNodeValue());
			}
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("SampleTime")) {
				parameters.put("st", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String offset = "(Real " + super.getParameters().get("offset") + ")";

		ret.put("init", "");
		ret.put("0", Out1 + "=1");
		ret.put("0b", In1 + "=" + offset);
		ret.put("1", Out1 + "=0");
		ret.put("1b", In1 + "!=" + offset);
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String offset = "(Real " + super.getParameters().get("offset") + ")";

		String ret1 = "(" + In1 + "=" + offset + ") -> " + Out1 + ":=1";
		String ret2 = "(" + In1 + "!=" + offset + ") -> " + Out1 + ":=0";
		ret.put("fun", ret1 + "; " + ret2);
		return ret;
	}

}
