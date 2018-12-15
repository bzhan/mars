package model.stateflow;

import java.util.ArrayList;
import java.util.HashMap;

import model.Utilize;

import org.w3c.dom.Node;

public class SF_Diagram {
	private String compositeType;
	private ArrayList<String> path;
	private int size = 0;
	// variables and events
	private ArrayList<String> cNames = new ArrayList<String>();
	private ArrayList<String> cVals = new ArrayList<String>();
	private ArrayList<String> iVars = new ArrayList<String>();
	private ArrayList<String> oVars = new ArrayList<String>();
	private ArrayList<String> lVars = new ArrayList<String>();
	private ArrayList<String> iVarsInit = new ArrayList<String>();
	private ArrayList<String> oVarsInit = new ArrayList<String>();
	private ArrayList<String> lVarsInit = new ArrayList<String>();
	private ArrayList<String> iEvents = new ArrayList<String>();
	private ArrayList<String> oEvents = new ArrayList<String>();
	private ArrayList<String> lEvents = new ArrayList<String>();

	public String getInit(HashMap<String, SF_Junction> locations) {
		String init = "";
		for (int i = 0; i < cNames.size(); i++) {
			if (cVals.get(i).equalsIgnoreCase(""))
				continue;
			init += "(" + cNames.get(i) + ":=(Real " + cVals.get(i) + "));";
			if (i % 6 == 5)
				init += "\n";
		}
		for (int i = 0; i < iVars.size(); i++) {
			if (iVarsInit.get(i).equalsIgnoreCase(""))
				continue;
			init += "(" + iVars.get(i) + ":=(Real " + iVarsInit.get(i) + "));";
			if (i % 6 == 5)
				init += "\n";
		}
		for (int i = 0; i < oVars.size(); i++) {
			if (oVarsInit.get(i).equalsIgnoreCase(""))
				continue;
			init += "(" + oVars.get(i) + ":=(Real " + oVarsInit.get(i) + "));";
			if (i % 6 == 5)
				init += "\n";
		}
		for (int i = 0; i < lVars.size(); i++) {
			if (lVarsInit.get(i).equalsIgnoreCase(""))
				continue;
			init += "(" + lVars.get(i) + ":=(Real " + lVarsInit.get(i) + "));";
			if (i % 6 == 5)
				init += "\n";
		}
		if (this.compositeType != null && this.compositeType.equals("OR")) {
			for (SF_Junction location : locations.values()) {
				// skip the locations that are not in this diagram
				if (!inDiagram(location) || !location.isState())
					continue;
				SF_State s = (SF_State) location;
				init += "(" + "act" + s.getName() + ":=(Real 0));";
			}
		}
		if (!init.endsWith("\n"))
			init += "\n";
		return init;
	}

	public SF_Diagram(Node node, HashMap<String, SF_Junction> locations,
			ArrayList<SF_Transition> transitions, String defaultSSID,
			ArrayList<String> path) {
		this.path = path;
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeName().equals("state")) {
				this.size++;
				if (n.getNodeType() == Node.ELEMENT_NODE
						&& n.getAttributes().getNamedItem("SSID") != null) {
					String SSID = n.getAttributes().getNamedItem("SSID")
							.getNodeValue();
					ArrayList<String> sPath = new ArrayList<String>(path);
					sPath.add(SSID);
					if (this.getNodeType(n).equals("FUNC")) {
						SF_Function function = new SF_Function(n, locations,
								sPath);
						locations.put(SSID, function);
					} else if (this.getNodeType(n).equals("AND")
							|| this.getNodeType(n).equals("OR")) {
						SF_State state = new SF_State(n, locations,
								transitions, sPath);
						locations.put(SSID, state);
						this.compositeType = state.getCompositeType();
					}
				} else {
					System.out
							.println("At least one state does not have a SSID!");
				}
			} else if (n.getNodeName().equals("junction")) {
				if (n.getNodeType() == Node.ELEMENT_NODE
						&& n.getAttributes().getNamedItem("SSID") != null) {
					String SSID = n.getAttributes().getNamedItem("SSID")
							.getNodeValue();
					ArrayList<String> sPath = new ArrayList<String>(path);
					sPath.add(SSID);
					SF_Junction junction = new SF_Junction(n, sPath);
					junction.setSSID("J" + SSID);
					locations.put(SSID, junction);
				} else {
					System.out
							.println("At least one junction does not have a SSID!");
				}
			} else if (n.getNodeName().equals("data")) {
				if (n.getNodeType() == Node.ELEMENT_NODE
						&& n.getAttributes().getNamedItem("name") != null) {
					String name = n.getAttributes().getNamedItem("name")
							.getNodeValue();
					String scope = "";
					String init = "";
					for (Node n1 = n.getFirstChild(); n1 != null; n1 = n1
							.getNextSibling()) {
						if (n1.getNodeType() == Node.ELEMENT_NODE
								&& n1.getAttributes().getNamedItem("Name") != null
								&& n1.getAttributes().getNamedItem("Name")
										.getNodeValue().equals("scope")) {
							scope = n1.getFirstChild().getNodeValue()
									.replaceAll("_DATA", "");
						} else if (n1.getNodeName().equals("props")) {
							for (Node n2 = n1.getFirstChild(); n2 != null; n2 = n2
									.getNextSibling()) {
								if (n2.getNodeType() == Node.ELEMENT_NODE
										&& n2.getAttributes().getNamedItem(
												"Name") != null
										&& n2.getAttributes()
												.getNamedItem("Name")
												.getNodeValue()
												.equals("initialValue"))
									init = n2.getFirstChild().getNodeValue();
							}
						}
					}
					if (scope.equalsIgnoreCase("CONSTANT")) {
						this.cNames.add(name);
						this.cVals.add(init);
					} else if (scope.equalsIgnoreCase("INPUT")) {
						this.iVars.add(name);
						this.iVarsInit.add(init);
					} else if (scope.equalsIgnoreCase("OUTPUT")) {
						this.oVars.add(name);
						this.oVarsInit.add(init);
					} else {
						this.lVars.add(name);
						this.lVarsInit.add(init);
					}
				}

			} else if (n.getNodeName().equals("event")) {
				String name = "";
				String scope = "";
				for (Node n1 = n.getFirstChild(); n1 != null; n1 = n1
						.getNextSibling()) {
					if (n1.getNodeType() == Node.ELEMENT_NODE
							&& n1.getAttributes().getNamedItem("Name") != null
							&& n1.getAttributes().getNamedItem("Name")
									.getNodeValue().equals("name")) {
						name = n1.getFirstChild().getNodeValue();
					} else if (n1.getNodeType() == Node.ELEMENT_NODE
							&& n1.getAttributes().getNamedItem("Name") != null
							&& n1.getAttributes().getNamedItem("Name")
									.getNodeValue().equals("scope")) {
						scope = n1.getFirstChild().getNodeValue()
								.replaceAll("_EVENT", "");
					}
				}
				if (scope.equalsIgnoreCase("LOCAL"))
					this.lEvents.add(name);
				else if (scope.equalsIgnoreCase("INPUT")) {
					this.iEvents.add(name);
				} else if (scope.equalsIgnoreCase("OUTPUT")) {
					this.oEvents.add(name);
				} else {
					System.out.println("An event does not belong to "
							+ "local, input, and output.");
				}
			}
		}

		// add an unique default junction
		if (this.compositeType != null && this.compositeType.equals("OR")) {
			ArrayList<String> sPath = new ArrayList<String>(path);
			sPath.add(defaultSSID);
			SF_Junction defaultJunction = new SF_Junction(sPath);
			defaultJunction.setSSID(defaultSSID);
			locations.put(defaultSSID, defaultJunction);
		}

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeName().equals("transition")) {
				SF_Transition transition = new SF_Transition(n);
				transitions.add(transition);
				if (transition.getSource().equals("-1")) {
					transition.setSource(defaultSSID);
				}
			}
		}
	}

	public boolean inDiagram(SF_Junction location) {
		ArrayList<String> sPath = new ArrayList<String>(location.getPath());
		if (sPath.size() != path.size() + 1)
			return false;
		for (int i = 0; i < path.size(); i++) {
			if (sPath.get(i) != path.get(i))
				return false;
		}
		return true;
	}

	public String getNodeType(Node node) {
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling())
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("Name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("type")) {
				return n.getFirstChild().getNodeValue()
						.replaceAll("_STATE", "");
			}
		return "";
	}

	public String getEntryProcess(HashMap<String, SF_Junction> locations) {
		String process = "";
		if (this.compositeType == null) {
			return process;
		} else if (this.compositeType.equals("OR")) {
			for (SF_Junction location : locations.values()) {
				// skip the locations that are not in this diagram or functions
				if (inDiagram(location) && location.getSSID().startsWith("D"))
					process += location.getTransProcess(locations, "event");
			}
		} else if (this.compositeType.equals("AND")) {
			HashMap<Integer, String> enProcesses = new HashMap<Integer, String>();
			for (SF_Junction location : locations.values()) {
				// skip the locations that are not in this diagram
				if (!inDiagram(location))
					continue;
				enProcesses.put(((SF_State) location).getOrder(),
						((SF_State) location).getEntryProcess(locations));
			}
			for (int i = 0; i < enProcesses.size(); i++)
				process += enProcesses.get(i);
		}
		return process;
	}

	public String getDuringProcess(Stateflow sf, HashMap<String, SF_Junction> locations,
			String event) {
		String process = "";
		if (this.compositeType == null) {
			return process;
		} else if (this.compositeType.equals("OR")) {
			for (SF_Junction location : locations.values()) {
				// skip the locations that are not in this diagram
				if (!inDiagram(location) || location.getSSID().startsWith("F")
						|| location.getSSID().startsWith("D")|| location.getSSID().startsWith("J"))
					continue;
				process += "IF ("
						+ ((SF_State) location).getIsActive()
						+ "[=](Real 1)) ("
						+ SFProcess.delTail(((SF_State) location)
								.getDuringProcess(sf, locations, event)) + ");\n";
			}
		} else if (this.compositeType.equals("AND")) {
			HashMap<Integer, String> enProcesses = new HashMap<Integer, String>();
			for (SF_Junction location : locations.values()) {
				// skip the locations that are not in this diagram
				if (!inDiagram(location))
					continue;
				enProcesses.put(((SF_State) location).getOrder(),
						((SF_State) location)
								.getDuringProcess(sf, locations, event));
			}
			for (int i = 1; i <= enProcesses.size(); i++)
				process += enProcesses.get(i);
		}
		return process;
	}

	public String getExitProcess(HashMap<String, SF_Junction> locations) {
		String process = "";
		if (this.compositeType == null) {
			return process;
		} else if (this.compositeType.equals("OR")) {
			for (SF_Junction location : locations.values()) {
				// skip the locations that are not in this diagram
				if (!inDiagram(location) || location.getSSID().startsWith("F")
						|| location.getSSID().startsWith("D"))
					continue;
				if (!((SF_State) location).getExitProcess(locations)
						.equalsIgnoreCase("")) {
					String exitPro = ((SF_State) location)
							.getExitProcess(locations);
					if (!exitPro.equalsIgnoreCase(""))
						exitPro = exitPro.substring(0, exitPro.length() - 1);
					process += "IF (" + ((SF_State) location).getIsActive()
							+ "[=](Real 1)) (" + exitPro + ");";
				}
			}
		} else if (this.compositeType.equals("AND")) {
			HashMap<Integer, String> enProcesses = new HashMap<Integer, String>();
			for (SF_Junction location : locations.values()) {
				// skip the locations that are not in this diagram
				if (!inDiagram(location))
					continue;
				enProcesses.put(((SF_State) location).getOrder(),
						((SF_State) location).getExitProcess(locations));
			}
			for (int i = 0; i < enProcesses.size(); i++)
				process += enProcesses.get(i);
		}
		return process;
	}

	// get and set functions
	public String getCompositeType() {
		return compositeType;
	}

	public void setCompositeType(String compositeType) {
		this.compositeType = compositeType;
	}

	public ArrayList<String> getPath() {
		return path;
	}

	public void setPath(ArrayList<String> path) {
		this.path = path;
	}

	public ArrayList<String> getcNames() {
		return cNames;
	}

	public ArrayList<String> getcVals() {
		return this.cVals;
	}

	public ArrayList<String> getIvars() {
		return this.iVars;
	}

	public ArrayList<String> getOvars() {
		return this.oVars;
	}

	public ArrayList<String> getLvars() {
		return this.lVars;
	}

	public ArrayList<String> getIvarsInit() {
		return iVarsInit;
	}

	public ArrayList<String> getOvarsInit() {
		return oVarsInit;
	}

	public ArrayList<String> getLvarsInit() {
		return lVarsInit;
	}

	public ArrayList<String> getIEvents() {
		return this.iEvents;
	}

	public ArrayList<String> getOEvents() {
		return this.oEvents;
	}

	public ArrayList<String> getLEvents() {
		return this.lEvents;
	}

	public int getSize() {
		return size;
	}

	// for print
	public void print(HashMap<String, SF_Junction> locations, int level) {
		String head = Utilize.tabsAhead(level);
		if (this.compositeType != null)
			System.out.println(head + "compositeType:\t" + this.compositeType);
		for (SF_Junction location : locations.values()) {
			// skip the locations that are not in this diagram
			if (!inDiagram(location))
				continue;

			// print locations, functions are printed later
			if (location.getSSID().startsWith("S"))
				((SF_State) location).print(locations, level);
			else if (location.getSSID().startsWith("J")
					|| location.getSSID().startsWith("D"))
				location.print(level);
			else if (location.getSSID().startsWith("F"))
				continue;
			else {
				System.out.println("A location that does not belong to "
						+ "state, junction, and function.");
				return;
			}

			// print transitions
			for (SF_Transition t : location.getOutsideOTrans()) {
				System.out.print(head + "OOuts:\t");
				t.print(locations);
			}
			for (SF_Transition t : location.getInsideOTrans()) {
				System.out.print(head + "IOuts:\t");
				t.print(locations);
			}
			// for (SF_Transition t : location.getInTranstions()) {
			// System.out.print(head + "Ins:\t");
			// t.print(locations);
			// }

			System.out.println();
		}

		// print functions
		// for (SF_Junction location : locations.values()) {
		// // skip the locations that are not in this diagram
		// if (!inDiagram(location))
		// continue;
		//
		// // print functions
		// if (location.getSSID().startsWith("F"))
		// location.print(level);
		//
		// System.out.println();
		// }

		// print constants
		for (int i = 0; i < this.cVals.size(); i++)
			System.out.println(head + "cVar(" + this.cNames.get(i) + "):\t"
					+ this.cVals.get(i));
		// print variables
		for (int i = 0; i < this.lVars.size(); i++)
			System.out.println(head + "lVar(" + this.lVars.get(i) + "):\t"
					+ this.lVarsInit.get(i));
		for (int i = 0; i < this.iVars.size(); i++)
			System.out.println(head + "iVar(" + this.iVars.get(i) + "):\t"
					+ this.iVarsInit.get(i));
		for (int i = 0; i < this.oVars.size(); i++)
			System.out.println(head + "oVar(" + this.oVars.get(i) + "):\t"
					+ this.oVarsInit.get(i));
		// print events
		for (int i = 0; i < this.lEvents.size(); i++)
			System.out.println(head + "lEvent:\t" + this.lEvents.get(i));
		for (int i = 0; i < this.iEvents.size(); i++)
			System.out.println(head + "iEvent:\t" + this.iEvents.get(i));
		for (int i = 0; i < this.oEvents.size(); i++)
			System.out.println(head + "oEvent:\t" + this.oEvents.get(i));

	}

}
