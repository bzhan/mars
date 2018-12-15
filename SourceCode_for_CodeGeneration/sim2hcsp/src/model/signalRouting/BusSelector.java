package model.signalRouting;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class BusSelector extends SL_Block {

	public BusSelector(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("st", "0");
		super.setParameters(parameters);

	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String min = super.getParameters().get("min");
		String max = super.getParameters().get("max");

		ret.put("init", "");
		ret.put("0", Out1 + "=" + In1);
		ret.put("0b", min + "<=" + In1 + "<=" + max);
		ret.put("1", Out1 + "=" + max);
		ret.put("1b", In1 + ">" + max);
		ret.put("2", Out1 + "=" + min);
		ret.put("2b", In1 + "<" + min);
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		String In1 = super.getinVarNames().get(1);
		String Out1 = super.getName() + "_1";
		String min = super.getParameters().get("min");
		String max = super.getParameters().get("max");

		String ret1 = "(" + min + "<=" + In1 + "<=" + max + ") -> " + Out1 + ":=" + In1;
		String ret2 = "(" + In1 + ">" + max + ") -> " + Out1 + ":=" + max;
		String ret3 = "(" + In1 + "<" + min + ") -> " + Out1 + ":=" + min;
		ret.put("fun", ret1 + "; " + ret2 + "; " + ret3);
		return ret;
	}

}
