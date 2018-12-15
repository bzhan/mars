package model.signalRouting;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Mux extends SL_Block {

	public Mux(String blockType, String blockName, Node node) {
		super(blockType, blockName);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("num", "1");
		parameters.put("st", "0");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Inputs")) {
				parameters.put("num", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		HashMap<Integer, String> Ins = super.getinVarNames();
		String Out1 = super.getName() + "_1";
		int num = Integer.parseInt(super.getParameters().get("num"));
		String str = "";

		for (int i = 0; i < num; i++) {
			str += Out1 + "[" + i + "]=" + Ins.get(i);
		}

		ret.put("init", "");
		ret.put("0", str);
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		HashMap<Integer, String> Ins = super.getinVarNames();
		String Out1 = super.getName() + "_1";
		int num = Integer.parseInt(super.getParameters().get("num"));
		String str = "";

		for (int i = 0; i < num; i++) {
			str += Out1 + "[" + i + "]:=" + Ins.get(i);
		}

		ret.put("fun", str);
		return ret;
	}

}
