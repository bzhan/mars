package model.stateflow;

import java.util.HashMap;

import org.w3c.dom.Node;

public class SF_Transition {
	private String source;
	private String target;
	private String event = "";
	private String condition = "";
	private String cAction = "";
	private String tAction = "";
	private int order;

	public SF_Transition() {
	}

	public SF_Transition(Node node) {
		this.source = "-1";
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeName().equals("src")) {
				for (Node n1 = n.getFirstChild(); n1 != null; n1 = n1
						.getNextSibling()) {
					if (n1.getNodeType() == Node.ELEMENT_NODE
							&& n1.getAttributes().getNamedItem("Name") != null
							&& n1.getAttributes().getNamedItem("Name")
									.getNodeValue().equals("SSID")) {
						this.source = n1.getFirstChild().getNodeValue();
					}
				}
			} else if (n.getNodeName().equals("dst")) {
				for (Node n1 = n.getFirstChild(); n1 != null; n1 = n1
						.getNextSibling()) {
					if (n1.getNodeType() == Node.ELEMENT_NODE
							&& n1.getAttributes().getNamedItem("Name") != null
							&& n1.getAttributes().getNamedItem("Name")
									.getNodeValue().equals("SSID")) {
						this.target = n1.getFirstChild().getNodeValue();
					}
				}
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("labelString") && n.getFirstChild() != null) {
				String labelString = n.getFirstChild().getNodeValue();
				this.constructTransitions(labelString);
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("executionOrder")) {
				this.order = Integer.valueOf(n.getFirstChild().getNodeValue());
			}
		}
	}

	public SF_Transition(String source, String target, String event,
			String condition, String cAction, String tAction, int order) {
		this.source = source;
		this.target = target;
		this.event = event;
		this.condition = SFProcess.grd2HCSP(condition);
		this.cAction = SFProcess.act2HCSP(cAction);
		this.tAction = SFProcess.act2HCSP(tAction);
		this.order = order;
	}

	private void constructTransitions(String labelString) {
		if (labelString.contains("[")) {
			this.condition = SFProcess.grd2HCSP(labelString.substring(
					labelString.indexOf("[") + 1, labelString.indexOf("]")));
			labelString = labelString.substring(0, labelString.indexOf("["))
					+ labelString.substring(labelString.indexOf("]") + 1,
							labelString.length());
		}
		if (labelString.contains("{")) {
			this.cAction = SFProcess.act2HCSP(labelString.substring(
					labelString.indexOf("{") + 1, labelString.indexOf("}")));
			labelString = labelString.substring(0, labelString.indexOf("{"))
					+ labelString.substring(labelString.indexOf("}") + 1,
							labelString.length());
		}
		if (labelString.contains("/")) {
			this.tAction = SFProcess.act2HCSP(labelString.substring(
					labelString.indexOf("/") + 1, labelString.length()));
			labelString = labelString.substring(0, labelString.indexOf("/"));
		}
		this.event = labelString;
	}

	public boolean isSTransition() {
		return false;
	}

	public String getSTransitionProcess(String event) {
		// TODO: this will be done when considering hierarchy states
		return "";
	}

	// get and set functions
	public String getEvent() {
		return event;
	}

	public void setEvent(String event) {
		this.event = event;
	}

	public String getCondition() {
		return this.condition;
	}

	public void setCondition(String condition) {
		this.condition = condition;
	}

	public String getcAction() {
		return this.cAction;
	}

	public void setcAction(String cAction) {
		this.cAction = cAction;
	}

	public String gettAction() {
		return this.tAction;
	}

	public void settAction(String tAction) {
		this.tAction = tAction;
	}

	public String getSource() {
		return this.source;
	}

	public void setSource(String source) {
		this.source = source;
	}

	public String getTarget() {
		return this.target;
	}

	public void setTarget(String target) {
		this.target = target;
	}

	public int getOrder() {
		return order;
	}

	public void setOrder(int order) {
		this.order = order;
	}

	// for print
	public void print(HashMap<String, SF_Junction> locations) {
		String start = this.source;
		String end = this.target;
		if (locations.get(this.source).getSSID().startsWith("S"))
			start = locations.get(this.source).getName();
		if (locations.get(this.target).getSSID().startsWith("S"))
			end = locations.get(this.target).getName();
		String transition = start + "(" + order + ")--" + this.event + "["
				+ this.condition + "]{" + this.cAction + "}/" + this.tAction
				+ "-->" + end;
		System.out.println(transition.replaceAll("\\[\\]", "")
				.replaceAll("\\{\\}", "").replaceAll("/--", "--"));
	}
}
