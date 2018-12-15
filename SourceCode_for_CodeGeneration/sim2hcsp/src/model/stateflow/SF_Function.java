package model.stateflow;

import java.util.ArrayList;
import java.util.HashMap;

import model.Utilize;

import org.w3c.dom.Node;

public class SF_Function extends SF_Junction {
	private String name;
	private String Fun;

	public SF_Function(Node node, HashMap<String, SF_Junction> locations,
			ArrayList<String> path) {
		super(node, path);
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeName().equals("eml")) {
				for (Node n1 = n.getFirstChild(); n1 != null; n1 = n1
						.getNextSibling()) {
					if (n1.getNodeType() == Node.ELEMENT_NODE
							&& n1.getAttributes().getNamedItem("Name") != null
							&& n1.getAttributes().getNamedItem("Name")
									.getNodeValue().equals("script")) {
						this.Fun = n1.getFirstChild().getNodeValue()
								.replaceAll("\n\n", "\n");
					}
				}
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("labelString")) {
				this.name = n.getFirstChild().getNodeValue();
			}
		}
		super.setSSID("F" + super.getSSID());
	}

	public String getFun() {
		return this.Fun;
	}

	public String getName() {
		return name;
	}

	// for print
	public void print(int level) {
		String head = Utilize.tabsAhead(level);
		System.out.println(head + "Fun(" + name + "):\n" + this.Fun);
	}

}
