package model.sinks;

import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Terminator extends SL_Block {

	public Terminator(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();
		parameters.put("st", "0");
		super.setParameters(parameters);
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		HashMap<String, String> ret = new HashMap<String, String>();

		ret.put("init", "");
		ret.put("0", "Stop");
		ret.put("0b", "");
		return ret;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();

		ret.put("fun", "Skip");
		return ret;
	}

}
