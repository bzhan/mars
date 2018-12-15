
package model.mathOperations;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Sign extends SL_Block {

	public Sign(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("st", "-1");

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE && n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue().equals("SampleTime")) {
				parameters.put("st", n.getFirstChild().getNodeValue());
			}
		}
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";

		ret.put("init", "");
		ret.put("0", Out1 + "=1");
		ret.put("0b", In1 + ">0");
		ret.put("1", Out1 + "=-1");
		ret.put("1b", In1 + "<0");
		ret.put("2", Out1 + "=0");
		ret.put("2b", In1 + "=0");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";

		String ret1 = "(" + In1 + ">0" + ") -> " + Out1 + ":=(Real 1)";
		String ret2 = "(" + In1 + "<0" + ") -> " + Out1 + ":=(Real --1)";
		String ret3 = "(" + In1 + "=0" + ") -> " + Out1 + ":=(Real 0)";
		ret.put("fun", ret1 + "; " + ret2 + "; " + ret3);
		return ret;
	}

}
