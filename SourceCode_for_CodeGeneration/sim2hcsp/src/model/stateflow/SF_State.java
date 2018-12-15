package model.stateflow;

import java.util.ArrayList;
import java.util.HashMap;

import m2h.SL2HCSP;
import model.Utilize;

import org.w3c.dom.Node;

public class SF_State extends SF_Junction {
	private String name;
	private String compositeType;
	private String isActive;
	private int order;
	private SF_Diagram diagram;
	// entry, exit, during actions; and on, bind event
	private HashMap<String, String> actions = new HashMap<String, String>();

	public SF_State(Node node, HashMap<String, SF_Junction> locations,
			ArrayList<SF_Transition> transitions, ArrayList<String> path) {
		super(node, path);
		this.order = 0;
		// get info
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("labelString")) {
				String labelString = n.getFirstChild().getNodeValue();
				this.constructActions(labelString);
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("type")) {
				this.compositeType = n.getFirstChild().getNodeValue()
						.replaceAll("_STATE", "");
			} else if (n.getNodeName().equals("Children")) {
				this.diagram = new SF_Diagram(n, locations, transitions, "D"
						+ super.getSSID(), path);
			} else if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("executionOrder")) {
				this.order = Integer.valueOf(n.getFirstChild().getNodeValue());
			}
		}
		super.setSSID("S" + super.getSSID());
		this.isActive = "act" + this.getName();
	}

	private void constructActions(String labelString) {
		if (labelString.contains(":")) {
			this.name = labelString.substring(0, labelString.indexOf(":"));
			this.name = this.name.substring(0, this.name.indexOf("\n") + 1)
					.replaceAll("\n", "");
		} else {
			this.name = labelString;
		}
		labelString = labelString.substring(this.name.length(),
				labelString.length());
		while (labelString.contains(":")) {
			String head = labelString.substring(0, labelString.indexOf(":"));
			labelString = labelString.substring(labelString.indexOf(":") + 1,
					labelString.length());
			String action = "";
			if (labelString.contains(":")) {
				action = labelString.substring(0, labelString.indexOf(":"));
				action = action.substring(0, action.lastIndexOf(";") + 1);
				labelString = labelString.substring(action.length(),
						labelString.length());
			} else {
				action = labelString;
				labelString = "";
			}
			head = head.replaceAll("entry", "en").replaceAll("during", "du")
					.replaceAll("exit", "ex").replaceAll("\n", "")
					.replace(" ", "");
			this.actions.put(head, action);
		}
	}

	public String getEntryProcess(HashMap<String, SF_Junction> locations) {
		String process = "";
		if (!this.getEn().equalsIgnoreCase(""))
			process = this.getEn() + ";";
		process += this.isActive + ":=(Real 1);";
		if (this.diagram != null)
			process += this.diagram.getEntryProcess(locations);
		return process;
	}

	public String getDuringProcess(Stateflow sf,
			HashMap<String, SF_Junction> locations, String event) {
		String process = "";
		process += getTransProcess(sf, locations, super.getOutsideOTrans(),
				event);
		if (!getTransProcess(sf, locations, super.getInsideOTrans(), event)
				.equalsIgnoreCase(""))
			process += getTransProcess(sf, locations, super.getInsideOTrans(),
					event);
		String sub = "";
		if (actions.containsKey("du"))
			sub += this.actions.get("du");
		if (this.diagram != null)
			sub += this.diagram.getDuringProcess(sf, locations, event);
		if (!sub.equalsIgnoreCase(""))
			process += "IF (" + event.replaceAll("E", "done")
					+ "[=](Real 0)) (" + sub + ")";
		return process;
	}

	public String getExitProcess(HashMap<String, SF_Junction> locations) {
		String process = "";
		if (!this.getEx().equalsIgnoreCase(""))
			process = this.getEx() + ";";
		process += this.isActive + ":=(Real 0);";
		if (this.diagram != null)
			process = this.diagram.getExitProcess(locations) + process;
		return process;
	}

	public String getTransProcess(Stateflow sf,
			HashMap<String, SF_Junction> locations,
			ArrayList<SF_Transition> trans, String event) {
		if (SL2HCSP.sfNet)
			return this.getTransProcessNet(locations, trans, event);
		else {
			HashMap<String, String> pset = new HashMap<String, String>();
			String process = this.getTransProcessSep(sf, locations, trans,
					event, pset);
			if (!process.equalsIgnoreCase(""))
				return "ACT:=skip;" + process;
			else
				return "";
		}
	}

	public String getTransProcessSep(Stateflow sf,
			HashMap<String, SF_Junction> locations,
			ArrayList<SF_Transition> trans, String event,
			HashMap<String, String> pset) {

		String process = "";
		for (SF_Transition t : trans) {
			SF_Junction target = locations.get(t.getTarget());
			String newEvent = t.getEvent();
			boolean eNeedCheck = !newEvent.equalsIgnoreCase("");
			String newCond = t.getCondition();
			String newCA = t.getcAction();
			String newTA = t.gettAction();
			// update guard
			String guard = "";
			if (eNeedCheck) {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + event + "[=](String ''" + newEvent + "'')[&]"
							+ newCond + "[&]" + event.replaceAll("E", "done")
							+ "[=](Real 0))";
				else
					guard = "(" + event + "[=](String ''" + newEvent
							+ event.replaceAll("E", "done") + "[=](Real 0))[&]"
							+ "'')";
			} else {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + newCond + "[&]"
							+ event.replaceAll("E", "done") + "[=](Real 0))";
				else
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))";
			}
			if (!guard.equalsIgnoreCase(""))
				process += "IF (" + guard + ") (";
			else
				process += "(";
			// update action
			if (!newCA.equalsIgnoreCase(""))
				process += newCA;
			if (!newTA.equalsIgnoreCase(""))
				process += "ACT:=(ACT;" + newTA + ")";
			// this transition is end
			// if the junction is a state or end-up junction
			if (target.isState()) {
				// for exits and entries
				// common path location
				SF_State tState = (SF_State) locations.get(target.getSSID()
						.substring(1, target.getSSID().length()));
				ArrayList<String> newPath = tState.getPath();
				int startIndex = 0;
				for (; startIndex < newPath.size()
						&& startIndex < super.getPath().size(); startIndex++) {
					if (!newPath.get(startIndex).equals(
							super.getPath().get(startIndex))) {
						break;
					}
				}
				// exit
				process += this.getExitProcess(locations);
				for (int i = super.getPath().size() - 1; i >= startIndex; i--) {
					process += ((SF_State) locations
							.get(super.getPath().get(i))).getEx();
				}
				// transition actions
				process += "ACT;";
				// entry
				for (int i = startIndex; i < newPath.size(); i++) {
					process += ((SF_State) locations.get(newPath.get(i)))
							.getEn();
				}
				process += tState.getEntryProcess(locations);
				process += event.replaceAll("E", "done") + ":=(Real 1));\n";
			} else if (target.getOutsideOTrans().isEmpty()) {
				// this transition is deleted
				process = SFProcess.delTail(process) + ");\n";
			} else {
				if (!pset.containsKey(target.getName())) {
					pset.put(target.getName(), "");
					pset.put(
							target.getName(),
							getTransProcessSep(sf, locations,
									target.getOutsideOTrans(), event, pset));
					sf.processAss += "definition P" + target.getName()
							+ " :: proc where\n" + "\"P" + target.getName()
							+ "==" + pset.get(target.getName()) + "\n\n";
				}
				process = process + "P" + target.getName() + ");\n";
			}
		}

		return process;
	}

	public String getTransProcessSep1(Stateflow sf,
			HashMap<String, SF_Junction> locations,
			ArrayList<SF_Transition> trans, String event) {

		String process = "";

		// terminate when trans is empty
		if (trans.isEmpty())
			return process;

		// the definition
		SF_Junction src = locations.get(trans.get(0).getSource());
		for (SF_Transition t : src.getOutsideOTrans()) {
			SF_Junction nextJunction = locations.get(t.getTarget());
			String newEvent = t.getEvent();
			boolean eNeedCheck = !newEvent.equalsIgnoreCase("");
			String newCond = t.getCondition();
			String newCA = t.getcAction();
			String newTA = t.gettAction();
			// update guard
			String guard = "";
			if (eNeedCheck) {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + event + "[=](String ''"
							+ newEvent + "'')[&]" + newCond;
				else
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + event + "[=](String ''"
							+ newEvent + "'')";
			} else {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + newCond;
				else
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))";
			}
			if (!guard.equalsIgnoreCase(""))
				process += "IF (" + guard + ") (";
			else
				process += "(";
			// update action
			if (!newCA.equalsIgnoreCase(""))
				process += newCA;
			// this transition is end
			// if the junction is a state or end-up junction
			if (nextJunction.isState()) {
				// for exits and entries
				// common path location
				SF_State tState = (SF_State) locations.get(nextJunction
						.getSSID()
						.substring(1, nextJunction.getSSID().length()));
				ArrayList<String> newPath = tState.getPath();
				int startIndex = 0;
				for (; startIndex < newPath.size()
						&& startIndex < super.getPath().size(); startIndex++) {
					if (!newPath.get(startIndex).equals(
							super.getPath().get(startIndex))) {
						break;
					}
				}
				// exit
				process += this.getExitProcess(locations);
				for (int i = super.getPath().size() - 1; i >= startIndex; i--) {
					process += ((SF_State) locations
							.get(super.getPath().get(i))).getEx();
				}
				// entry
				for (int i = startIndex; i < newPath.size(); i++) {
					process += ((SF_State) locations.get(newPath.get(i)))
							.getEn();
				}
				process += tState.getEntryProcess(locations);
				process += newTA;
				process += event.replaceAll("E", "done") + ":=(Real 1));\n";
			} else if (nextJunction.getOutsideOTrans().isEmpty()) {
				// this transition is deleted
				process = SFProcess.delTail(process) + ");\n";
			} else {
				process = process + "P" + nextJunction.getSSID() + ");\n";
			}
		}

		// dfs search heap
		ArrayList<SF_Junction> heap = new ArrayList<SF_Junction>();
		heap.add(locations.get(trans.get(0).getSource()));
		// Event list for the search heap
		ArrayList<String> eList = new ArrayList<String>();
		eList.add("");
		// Current branches list for the search heap
		ArrayList<Integer> searchLoc = new ArrayList<Integer>();
		searchLoc.add(0);

		// Data that will be update during the search
		ArrayList<String> tActions = new ArrayList<String>();

		// the search
		while (!heap.isEmpty()) {
			SF_Junction head = heap.get(heap.size() - 1);
			int headLoc = searchLoc.get(searchLoc.size() - 1);
			// skip if searchLoc is too big
			if (heap.size() > 1 && headLoc >= head.getOutsideOTrans().size()
					|| heap.size() <= 1 && headLoc >= trans.size()) {
				heap.remove(heap.size() - 1);
				if (heap.isEmpty()) {
					// process = SFProcess.delTail(process) + ");\n";
					break;
				}
				searchLoc.remove(searchLoc.size() - 1);
				searchLoc.set(searchLoc.size() - 1,
						searchLoc.get(searchLoc.size() - 1) + 1);
				eList.remove(eList.size() - 1);
				tActions.remove(tActions.size() - 1);
				continue;
			}
			// skip when it is not a junction
			if (head.isState())
				continue;
			sf.processAss += "definition P" + head.getSSID()
					+ " :: proc where\n" + "\"P" + head.getSSID() + "==";
			// prepare
			SF_Transition t = new SF_Transition();
			if (heap.size() == 1) {
				t = trans.get(headLoc);
			} else {
				t = head.getOutsideOTrans().get(headLoc);
			}
			SF_Junction nextJunction = locations.get(t.getTarget());
			String newEvent = t.getEvent();
			boolean eNeedCheck = true;
			String newCond = t.getCondition();
			String newCA = t.getcAction();
			String newTA = t.gettAction();
			// Deal with event
			if (!eList.get(eList.size() - 1).equalsIgnoreCase("")) {
				eNeedCheck = false;
				if (newEvent.equalsIgnoreCase("")) {
					newEvent = eList.get(eList.size() - 1);
				} else if (!newEvent
						.equalsIgnoreCase(eList.get(eList.size() - 1))) {
					// this transition is deleted
					searchLoc.set(searchLoc.size() - 1, ++headLoc);
					continue;
				}
			}
			if (newEvent.equalsIgnoreCase(""))
				eNeedCheck = false;
			// update guard
			String guard = "";
			if (eNeedCheck) {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + event + "[=](String ''"
							+ newEvent + "'')[&]" + newCond;
				else
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + event + "[=](String ''"
							+ newEvent + "'')";
			} else {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + newCond;
				else
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))";
			}
			if (!guard.equalsIgnoreCase(""))
				sf.processAss += "IF (" + guard + ") (";
			else
				sf.processAss += "(";
			// update action
			if (!newCA.equalsIgnoreCase(""))
				sf.processAss += newCA;
			// this transition is end
			// if the junction is a state or end-up junction
			if (nextJunction.isState()) {
				// for exits and entries
				// common path location
				SF_State tState = (SF_State) locations.get(nextJunction
						.getSSID()
						.substring(1, nextJunction.getSSID().length()));
				ArrayList<String> newPath = tState.getPath();
				int startIndex = 0;
				for (; startIndex < newPath.size()
						&& startIndex < super.getPath().size(); startIndex++) {
					if (!newPath.get(startIndex).equals(
							super.getPath().get(startIndex))) {
						break;
					}
				}
				// exit
				sf.processAss += this.getExitProcess(locations);
				for (int i = super.getPath().size() - 1; i >= startIndex; i--) {
					sf.processAss += ((SF_State) locations.get(super.getPath()
							.get(i))).getEx();
				}
				// entry
				for (int i = startIndex; i < newPath.size(); i++) {
					sf.processAss += ((SF_State) locations.get(newPath.get(i)))
							.getEn();
				}
				sf.processAss += tState.getEntryProcess(locations);
				sf.processAss += getNewTAs(tActions, newTA);
				sf.processAss += event.replaceAll("E", "done")
						+ ":=(Real 1));\n";
				searchLoc.set(searchLoc.size() - 1, ++headLoc);
				continue;
			} else if (nextJunction.getOutsideOTrans().isEmpty()) {
				// this transition is deleted
				sf.processAss = SFProcess.delTail(sf.processAss) + ");\n";
				searchLoc.set(searchLoc.size() - 1, ++headLoc);
				continue;
			}
			// add new head
			sf.processAss = sf.processAss + "P" + nextJunction.getSSID()
					+ ");\n";
			heap.add(nextJunction);
			searchLoc.add(0);
			eList.add(newEvent);
			tActions.add(newTA);
		}

		return process;
	}

	public String getTransProcessNet(HashMap<String, SF_Junction> locations,
			ArrayList<SF_Transition> trans, String event) {

		String process = "";

		// terminate when trans is empty
		if (trans.isEmpty())
			return process;

		// dfs search heap
		ArrayList<SF_Junction> heap = new ArrayList<SF_Junction>();
		heap.add(locations.get(trans.get(0).getSource()));
		// Event list for the search heap
		ArrayList<String> eList = new ArrayList<String>();
		eList.add("");
		// Current branches list for the search heap
		ArrayList<Integer> searchLoc = new ArrayList<Integer>();
		searchLoc.add(0);

		// Data that will be update during the search
		ArrayList<String> tActions = new ArrayList<String>();

		// the search
		while (!heap.isEmpty()) {
			SF_Junction head = heap.get(heap.size() - 1);
			int headLoc = searchLoc.get(searchLoc.size() - 1);
			// skip if searchLoc is too big
			if (heap.size() > 1 && headLoc >= head.getOutsideOTrans().size()
					|| heap.size() <= 1 && headLoc >= trans.size()) {
				heap.remove(heap.size() - 1);
				if (heap.isEmpty()) {
					// process = SFProcess.delTail(process) + ");\n";
					break;
				}
				searchLoc.remove(searchLoc.size() - 1);
				searchLoc.set(searchLoc.size() - 1,
						searchLoc.get(searchLoc.size() - 1) + 1);
				eList.remove(eList.size() - 1);
				tActions.remove(tActions.size() - 1);
				process = SFProcess.delTail(process) + ");\n";
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
			boolean eNeedCheck = true;
			String newCond = t.getCondition();
			String newCA = t.getcAction();
			String newTA = t.gettAction();
			// Deal with event
			if (!eList.get(eList.size() - 1).equalsIgnoreCase("")) {
				eNeedCheck = false;
				if (newEvent.equalsIgnoreCase("")) {
					newEvent = eList.get(eList.size() - 1);
				} else if (!newEvent
						.equalsIgnoreCase(eList.get(eList.size() - 1))) {
					// this transition is deleted
					searchLoc.set(searchLoc.size() - 1, ++headLoc);
					continue;
				}
			}
			if (newEvent.equalsIgnoreCase(""))
				eNeedCheck = false;
			// update guard
			String guard = "";
			if (eNeedCheck) {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + event + "[=](String ''"
							+ newEvent + "'')[&]" + newCond;
				else
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + event + "[=](String ''"
							+ newEvent + "'')";
			} else {
				if (!newCond.equalsIgnoreCase(""))
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))[&]" + newCond;
				else
					guard = "(" + event.replaceAll("E", "done")
							+ "[=](Real 0))";
			}
			if (!guard.equalsIgnoreCase(""))
				process += "IF (" + guard + ") (";
			else
				process += "(";
			// update action
			if (!newCA.equalsIgnoreCase(""))
				process += newCA;
			// this transition is end
			// if the junction is a state or end-up junction
			if (nextJunction.isState()) {
				// for exits and entries
				// common path location
				SF_State tState = (SF_State) locations.get(nextJunction
						.getSSID()
						.substring(1, nextJunction.getSSID().length()));
				ArrayList<String> newPath = tState.getPath();
				int startIndex = 0;
				for (; startIndex < newPath.size()
						&& startIndex < super.getPath().size(); startIndex++) {
					if (!newPath.get(startIndex).equals(
							super.getPath().get(startIndex))) {
						break;
					}
				}
				// exit
				process += this.getExitProcess(locations);
				for (int i = super.getPath().size() - 1; i >= startIndex; i--) {
					process += ((SF_State) locations
							.get(super.getPath().get(i))).getEx();
				}
				// entry
				for (int i = startIndex; i < newPath.size(); i++) {
					process += ((SF_State) locations.get(newPath.get(i)))
							.getEn();
				}
				process += tState.getEntryProcess(locations);
				process += getNewTAs(tActions, newTA);
				process += event.replaceAll("E", "done") + ":=(Real 1));\n";
				searchLoc.set(searchLoc.size() - 1, ++headLoc);
				continue;
			} else if (nextJunction.getOutsideOTrans().isEmpty()) {
				// this transition is deleted
				process = SFProcess.delTail(process) + ");\n";
				searchLoc.set(searchLoc.size() - 1, ++headLoc);
				continue;
			}
			// add new head
			heap.add(nextJunction);
			searchLoc.add(0);
			eList.add(newEvent);
			tActions.add(newTA);
		}
		return process;
	}

	String getNewTAs(ArrayList<String> tActions, String newTA) {
		String str = "";
		for (int i = 1; i < tActions.size(); i++) {
			if (!tActions.get(i).equalsIgnoreCase(""))
				str += tActions.get(i) + ";";
		}
		return str + newTA;
	}

	public boolean isState() {
		return true;
	}

	// get and set functions
	public String getCompositeType() {
		return compositeType;
	}

	public HashMap<String, String> getActions() {
		return actions;
	}

	public String getEn() {
		if (this.actions.containsKey("en"))
			return SFProcess.act2HCSP(this.actions.get("en"));
		else
			return "";
	}

	public String getDu() {
		if (this.actions.containsKey("du"))
			return SFProcess.act2HCSP(this.actions.get("du"));
		else
			return "";
	}

	public String getEx() {
		if (this.actions.containsKey("ex"))
			return SFProcess.act2HCSP(this.actions.get("ex"));
		else
			return "";
	}

	public SF_Diagram getDiagram() {
		return diagram;
	}

	public void setDiagram(SF_Diagram diagram) {
		this.diagram = diagram;
	}

	public int getOrder() {
		return order;
	}

	public void setOrder(int order) {
		this.order = order;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getIsActive() {
		return isActive;
	}

	// for print
	public void print(HashMap<String, SF_Junction> locations, int level) {
		String head = Utilize.tabsAhead(level);
		System.out.println(head + "name:\t" + this.name);
		if (this.compositeType.equals("AND")) {
			System.out.println(head + "order:\t" + this.order);
		}
		for (String key : this.actions.keySet()) {
			System.out.println(head + key + " action:\t"
					+ this.actions.get(key));
		}
		if (this.diagram != null)
			this.diagram.print(locations, level + 1);
	}

}
