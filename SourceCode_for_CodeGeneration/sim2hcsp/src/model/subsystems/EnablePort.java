package model.subsystems;

import org.w3c.dom.Node;

import model.SL_Block;

public class EnablePort extends SL_Block {

	public EnablePort(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		parameters.put("st", "-1");
	}

}
