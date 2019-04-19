package model.stateflow;

import java.util.ArrayList;
import java.util.HashMap;

import org.w3c.dom.Node;

import model.SL_Block;

public class Stateflow extends SL_Block {
	private SF_Diagram diagram;
	private HashMap<String, SF_Junction> locations = new HashMap<String, SF_Junction>();
	private ArrayList<SF_Transition> transitions = new ArrayList<SF_Transition>();
	public String processAss;

	public Stateflow(String blockName, Node node) {
		super("Stateflow", blockName);
		ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
		outTypes.add(false);
		super.setOutTypes(outTypes);
		processAss = "";
		
		String defaultSSID = "D" + node.getAttributes().getNamedItem("id").getNodeValue();
		ArrayList<String> path = new ArrayList<String>();

		super.parameters.put("st", "-1");
		Node diagNode = null;
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("sampleTime")) {
				parameters.put("st", n.getFirstChild().getNodeValue());
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("updateMethod")) {
				String method = n.getFirstChild().getNodeValue(); // CONTINUOUS
				if (method != "DISCRETE") {
					parameters.put("st", "-1");
				}
			} else if (n.getNodeName() != null && n.getNodeName() == "Children") {
				diagNode = n; // <chart><Children>
			}
		}

		if (diagNode == null)
			System.out.println("Stateflow Chart " + blockName + " is emplty!");
		else {
			this.diagram = new SF_Diagram(diagNode, locations, transitions, defaultSSID, path);
		}

		for (SF_Transition t : transitions) {
			// Distinguish outside and inside transitions
			int outOrIn = isOut(locations, t);
			t.setOrder(outOrIn * t.getOrder());
			// adherent transitions to locations
			String source = t.getSource();
			String target = t.getTarget();
			locations.get(target).getInTranstions().add(t);
			if (t.getOrder() > 0)
				locations.get(source).getOutsideOTrans().add(t);
			else if (t.getOrder() < 0)
				locations.get(source).getInsideOTrans().add(t);
		}

		// reorder out transitions for locations
		for (SF_Junction loc : locations.values()) {
			loc.reorderInsideOTrans();
			loc.reorderOutsideOTrans();
		}
	}

	private int isOut(HashMap<String, SF_Junction> locations, SF_Transition t) {
		ArrayList<String> path1 = new ArrayList<String>(locations.get(
				t.getSource()).getPath());
		ArrayList<String> path2 = new ArrayList<String>(locations.get(
				t.getTarget()).getPath());
		if (path2.size() < path1.size())
			return 1;
		for (int i = 0; i < path1.size(); i++) {
			if (path1.get(i) != path2.get(i))
				return 1;
		}
		return -1;
	}

	public void delJunctions(HashMap<String, SF_Junction> locations) {
		System.out
				.println("Function delJunctions is discarded, do not use it.");
		for (SF_Junction state : locations.values()) {
			if (!state.isState())
				continue;
			simpTranstions(locations, state.getOutsideOTrans());
			simpTranstions(locations, state.getInsideOTrans());
		}
	}

	public void simpTranstions(HashMap<String, SF_Junction> locations,
			ArrayList<SF_Transition> trans) {
		System.out
				.println("Function simpTranstions is discarded, do not use it.");

		// terminate when trans is empty
		if (trans.isEmpty())
			return;

		// dfs search heap
		ArrayList<SF_Junction> heap = new ArrayList<SF_Junction>();
		heap.add(locations.get(trans.get(0).getSource()));
		// Current branches list for the search heap
		ArrayList<Integer> searchLoc = new ArrayList<Integer>();
		searchLoc.add(0);
		// Event list for the search heap
		ArrayList<String> eList = new ArrayList<String>();
		eList.add("");

		// the search
		while (!heap.isEmpty()) {
			SF_Junction head = heap.get(heap.size() - 1);
			int headLoc = searchLoc.get(searchLoc.size() - 1);
			// skip if searchLoc is too big
			if (heap.size() > 1 && headLoc >= head.getOutsideOTrans().size()
					|| heap.size() <= 1 && headLoc >= trans.size()) {
				heap.remove(heap.size() - 1);
				if (heap.isEmpty())
					break;
				eList.remove(eList.size() - 1);
				searchLoc.remove(searchLoc.size() - 1);
				searchLoc.set(searchLoc.size() - 1,
						searchLoc.get(searchLoc.size() - 1) + 1);
				continue;
			}
			// prepare
			SF_Transition t = new SF_Transition();
			if (heap.size() == 1) {
				t = trans.get(headLoc);
			} else {
				t = head.getOutsideOTrans().get(headLoc);
			}
			SF_Junction nextJunction = locations.get(t.getTarget());
			String newEvent = t.getEvent();
			// Deal with event
			if (!eList.get(eList.size() - 1).equalsIgnoreCase("")) {
				if (newEvent.equalsIgnoreCase("")) {
					newEvent = eList.get(eList.size() - 1);
				} else if (!newEvent
						.equalsIgnoreCase(eList.get(eList.size() - 1))) {
					// this transition is deleted
					if (heap.size() == 1)
						trans.remove(headLoc);
					else
						locations.get(t.getSource()).getOutsideOTrans()
								.remove(headLoc);
					continue;
				}
			}
			// this transition is end
			// if the junction is a state or end-up junction
			if (nextJunction.isState()
					|| nextJunction.getOutsideOTrans().isEmpty()) {
				searchLoc.set(searchLoc.size() - 1, ++headLoc);
				continue;
			}
			// add new head
			heap.add(nextJunction);
			eList.add(newEvent);
			searchLoc.add(0);
		}
	}

	String getNewConds(ArrayList<String> conditions, String newCond) {
		String str = "";
		for (int i = 1; i < conditions.size(); i++) {
			str += conditions.get(i) + "[&]";
		}
		return str + newCond;
	}

	String getNewTAs(ArrayList<String> tActions, String newTA) {
		String str = "";
		for (int i = 1; i < tActions.size(); i++) {
			str += tActions.get(i) + ";";
		}
		return str + newTA;
	}

	// get and set functions
	public SF_Diagram getDiagram() {
		return diagram;
	}

	public void setDiagram(SF_Diagram diagram) {
		this.diagram = diagram;
	}

	public HashMap<String, SF_Junction> getLocations() {
		return locations;
	}

	public void setLocations(HashMap<String, SF_Junction> junctions) {
		this.locations = junctions;
	}

	// for print
	public void print() {
		this.diagram.print(locations, 0);
	}

}
