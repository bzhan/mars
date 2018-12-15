package model.sources;

import java.util.ArrayList;
import java.util.HashMap;

import model.SL_Block;

import org.w3c.dom.Node;

public class DiscretePulseGenerator extends SL_Block {

	public DiscretePulseGenerator(String blockType, String blockName, Node node) {
		super(blockType, blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);

		HashMap<String, String> parameters = new HashMap<String, String>();
		parameters.clear();

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("Amplitude")) {
				parameters.put("Amplitude", n.getFirstChild().getNodeValue());
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("Period")) {
				parameters.put("Period", n.getFirstChild().getNodeValue());
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("PulseWidth")) {
				parameters.put("PulseWidth", n.getFirstChild().getNodeValue());
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("PhaseDelay")) {
				parameters.put("PhaseDelay", n.getFirstChild().getNodeValue());
			}
		}
		
		parameters.put("st","1");
		super.setParameters(parameters);
	}

	// TODO: GCD of phaseDelay, pulseWidth, and period as its st.
	public HashMap<String, String> semanticFunctionDiscrete() {
		HashMap<String, String> ret = new HashMap<String, String>();
		String Out1 = super.getName() + "_1";
//		String amplitude = super.getParameters().get("Amplitude");
//		String period = super.getParameters().get("Period");
//		String pulseWidth = super.getParameters().get("PulseWidth");
//		String phaseDelay = super.getParameters().get("PhaseDelay");
		
		ret.put("init", "");
		ret.put("fun", Out1 + ":=1");
		return ret;
	}

}
