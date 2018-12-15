package model.signalRouting;

import java.util.HashMap;

import org.w3c.dom.Node;

public class Demux extends BusCreator {

	public Demux(String blockType, String blockName, Node node) {
		super(blockType, blockName, node);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("num", "2");
		parameters.put("st", "0");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("Outputs")) {
				parameters.put("num", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Outs = super.getName() + "_";
		int inSize = 4;
		int outSize = Integer.parseInt(super.getParameters().get("num"));

		int remain = inSize % outSize;
		String str = "";
		for (int i = 0, k = 0; i < outSize; i++) {
			int re = 0;
			if (i < remain)
				re = 1;
			for (int j = 0; j < inSize / outSize + re; j++) {
				str += Outs + i + "[" + j + "]=" + In1 + "[" + k + "]";
				k++;
			}
		}

		ret.put("init", "");
		ret.put("0", str);
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Outs = super.getName() + "_";
		int inSize = 4;
		int outSize = Integer.parseInt(super.getParameters().get("num"));

		int remain = inSize % outSize;
		String str = "";
		for (int i = 0, k = 0; i < outSize; i++) {
			int re = 0;
			if (i < remain)
				re = 1;
			for (int j = 0; j < inSize / outSize + re; j++) {
				str += Outs + i + "[" + j + "]=" + In1 + "[" + k + "]";
				k++;
			}
		}

		ret.put("fun", str);
		return ret;
	}

}
