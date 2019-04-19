package model.stateflow;

import java.util.ArrayList;
import java.util.HashMap;

import model.Utilize;

import org.w3c.dom.Node;

public class SF_Junction {
	private String SSID;
	private ArrayList<String> path;
	// private HashMap<Integer, SF_Transition> outTransitions = new
	// HashMap<Integer, SF_Transition>();
	private ArrayList<SF_Transition> outsideOTrans = new ArrayList<SF_Transition>();
	private ArrayList<SF_Transition> insideOTrans = new ArrayList<SF_Transition>();
	private ArrayList<SF_Transition> inTransitions = new ArrayList<SF_Transition>();

	public SF_Junction(ArrayList<String> path) {
		SSID = "-1";
		this.path = path;
	}

	public SF_Junction(Node n, ArrayList<String> path) {
		this.path = path;
		if (n.getNodeType() == Node.ELEMENT_NODE
				&& n.getAttributes().getNamedItem("SSID") != null) {
			this.SSID = n.getAttributes().getNamedItem("SSID").getNodeValue();
		}
	}

	public boolean isState() {
		return false;
	}

	public String getTransProcess(HashMap<String, SF_Junction> locations,
			String event) {

		ArrayList<SF_Transition> trans = this.getOutsideOTrans();
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
					//process = SFProcess.delTail(process) + ");\n";
					process += ");\n";
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
				} else if (!newEvent.equalsIgnoreCase(eList.get(eList.size() - 1))) {
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
					guard = event + "[=]" + newEvent + "[&]" + newCond;
				else
					guard = event + "[=]" + newEvent;
			} else {
				guard = newCond;
			}
			if (!guard.equalsIgnoreCase(""))
				process += "IF (" + guard + ") (";
			else
				process += "(";
			// update action
			if (!newCA.equalsIgnoreCase(""))
				process += newCA + ";";
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
						&& startIndex < this.getPath().size(); startIndex++) {
					if (!newPath.get(startIndex).equals(
							this.getPath().get(startIndex))) {
						break;
					}
				}
				// entry
				for (int i = startIndex; i < newPath.size(); i++) {
					process += ((SF_State) locations.get(newPath.get(i)))
							.getEn();
				}
				process += tState.getEntryProcess(locations);
				process += getNewTAs(tActions, newTA);
				//process = SFProcess.delTail(process);
				searchLoc.set(searchLoc.size() - 1, ++headLoc);
				continue;
			} else if (nextJunction.getOutsideOTrans().isEmpty()) {
				// this transition is deleted
				process += ");";
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
			str += tActions.get(i) + ";";
		}
		return str + newTA;
	}

	public void reorderOutsideOTrans() {
		for (int i = 0; i < outsideOTrans.size(); i++)
			for (int j = i + 1; j < outsideOTrans.size(); j++) {
				if (outsideOTrans.get(j).getOrder() - 1 == i) {
					outsideOTrans.add(i, outsideOTrans.get(j));
					outsideOTrans.remove(j + 1);
					break;
				}
			}
	}

	public void reorderInsideOTrans() {
		for (SF_Transition t : insideOTrans)
			t.setOrder(-1 * t.getOrder());
		for (int i = 0; i < insideOTrans.size(); i++)
			for (int j = i + 1; j < insideOTrans.size(); j++) {
				if (insideOTrans.get(j).getOrder() - 1 == i) {
					insideOTrans.add(i, insideOTrans.get(j));
					insideOTrans.remove(j + 1);
					break;
				}
			}
	}

	// get and set functions
	public String getName() {
		return "J" + SSID;
	}

	public String getSSID() {
		return SSID;
	}

	public void setSSID(String SSID) {
		this.SSID = SSID;
	}

	public ArrayList<SF_Transition> getInTranstions() {
		return inTransitions;
	}

	public ArrayList<String> getPath() {
		return path;
	}

	// for print
	public void print(int level) {
		String head = Utilize.tabsAhead(level);
		System.out.println(head + "SSID:\t" + this.SSID);
	}

	public ArrayList<SF_Transition> getOutsideOTrans() {
		return outsideOTrans;
	}

	public void setOutsideOTrans(ArrayList<SF_Transition> outsideOTrans) {
		this.outsideOTrans = outsideOTrans;
	}

	public ArrayList<SF_Transition> getInsideOTrans() {
		return insideOTrans;
	}

	public void setInsideOTrans(ArrayList<SF_Transition> insideOTrans) {
		this.insideOTrans = insideOTrans;
	}

}
