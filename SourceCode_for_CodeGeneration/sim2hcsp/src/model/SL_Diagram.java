package model;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;

import m2h.SL2HCSP;
import model.continuous.*;
import model.discontinuities.*;
import model.discrete.*;
import model.logicOperations.*;
import model.mathOperations.*;
import model.signalAttributes.*;
import model.signalRouting.*;
import model.sinks.*;
import model.sources.*;
import model.stateflow.Stateflow;
import model.subsystems.*;
import model.userDefinedBlocks.*;
import model.userDefinedFunctions.*;

import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class SL_Diagram {
	private HashMap<String, SL_Block> blocks = new HashMap<String, SL_Block>();
	private boolean broken;

	public SL_Diagram() {
	}

	public SL_Diagram(Node node, String diagLocation) {
		NodeList fstLayer = node.getChildNodes();
		if (fstLayer == null) {
			return;
		}

		for (int i = 0; i < fstLayer.getLength(); i++) {
			Node n = fstLayer.item(i);
			if (n.getNodeName().equals("Block")) {
				if (!analyzeBlock(n, diagLocation)) {
					broken = true;
					return;
				}
			}
		}

		for (int i = 0; i < fstLayer.getLength(); i++) {
			Node n = fstLayer.item(i);
			if (n.getNodeName().equals("Line")) { // n == <System><Line>
				analyzeLine(n);
			}
		}
		broken = false;
	}

	private boolean analyzeBlock(Node node, String diagLocation) {
		NamedNodeMap blockattributes = node.getAttributes();
		if (blockattributes == null) {
			System.out
					.println("A weird block exists, not any attribute exists.");
			return false;
		}

		String blocktype = blockattributes.getNamedItem("BlockType").getNodeValue();
		String blockname = blockattributes.getNamedItem("Name").getNodeValue().replaceAll(" |\n", "");

		// handle Stateflow diagrams
		if (S2M.getStateflows().containsKey(blockname)) {
			blocktype = "Stateflow";
		}

		// handle user defined blocks
		File f = new File(SL2HCSP.getUdsLocation() + diagLocation + blockname);
		if (f.exists()) {
			blocktype = "userDefinedBlock";
		}

		double blockst = -1; // block sample time?
		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE
					&& n.getAttributes().getNamedItem("name") != null
					&& n.getAttributes().getNamedItem("Name").getNodeValue()
							.equals("SampleTime")) {
				blockst = Double.valueOf(n.getFirstChild().getNodeValue());
			}
		}  // no sample time

		if (blocktype == null || blockname == null) {
			System.out.println("A weird block exists, name or type does not exists.");
			return false;
		}

		SL_Block block = newBlock(blocktype, blockname, node, blockst, diagLocation);
		if (block != null) {
			this.addBlock(blockname, block);
			return true;
		} else {
			System.out.println("Block analyze failed, block name is "
					+ blockname + ".");
			return false;
		}
	}

	private static SL_Block newBlock(String blocktype, String blockname, Node node, double st, String diagLocation) {
		// (blocktype = "Stateflow", blockname = "Chart", node = <System><Block>, st = -1, diagLocation = "")
		if (blocktype.equals("Abs")) {
			return new Abs(blocktype, blockname, node);
		} else if (blocktype.equals("Bias")) {
			return new Bias(blocktype, blockname, node);
		} else if (blocktype.equals("BusSelector")) {
			return new BusSelector(blocktype, blockname, node);
		} else if (blocktype.equals("BusCreator")) {
			return new BusCreator(blocktype, blockname, node);
		} else if (blocktype.equals("Clock")) {
			return new Clock(blocktype, blockname, node);
		} else if (blocktype.equals("CombinatorialLogic")) {
			return new CombinationalLogic(blocktype, blockname, node);
		} else if (blocktype.equals("Constant")) {
			return new Constant(blocktype, blockname, node);
		} else if (blocktype.equals("DataTypeConversion")) {
			return new DataTypeConversion(blocktype, blockname, node);
		} else if (blocktype.equals("DeadZone")) {
			return new DeadZone(blocktype, blockname, node);
		} else if (blocktype.equals("Demux")) {
			return new Demux(blocktype, blockname, node);
		} else if (blocktype.equals("Derivative")) {
			return new Derivative(blocktype, blockname, node);
		} else if (blocktype.equals("DigitalClock")) {
			return new DigitalClock(blocktype, blockname, node);
		} else if (blocktype.equals("DiscretePulseGenerator")) {
			return new DiscretePulseGenerator(blocktype, blockname, node);
		} else if (blocktype.equals("DiscreteIntegrator")) {
			return new DiscreteTimeIntegrator(blocktype, blockname, node);
		} else if (blocktype.equals("Display")) {
			return new Display(blocktype, blockname, node);
		} else if (blocktype.equals("DotProduct")) {
			return new DotProduct(blocktype, blockname, node);
		} else if (blocktype.equals("Fcn")) {
			return new Fcn(blocktype, blockname, node);
		} else if (blocktype.equals("Gain")) {
			return new Gain(blocktype, blockname, node);
		} else if (blocktype.equals("Ground")) {
			return new Ground(blocktype, blockname, node);
		} else if (blocktype.equals("HitCross")) {
			return new HitCrossing(blocktype, blockname, node);
		} else if (blocktype.equals("InitialCondition")) {
			return new IC(blocktype, blockname, node);
		} else if (blocktype.equals("Integrator")) {
			return new Integrator(blocktype, blockname, node);
		} else if (blocktype.equals("Logic")) {
			return new LogicalOperator(blocktype, blockname, node);
		} else if (blocktype.equals("Math")) {
			return new MathFunction(blocktype, blockname, node);
		} else if (blocktype.equals("Memory")) {
			return new Memory(blocktype, blockname, node);
		} else if (blocktype.equals("MinMax")) {
			return new MinMax(blocktype, blockname, node);
		} else if (blocktype.equals("Mux")) {
			return new Mux(blocktype, blockname, node);
		} else if (blocktype.equals("Product")) {
			return new Divide(blocktype, blockname, node);
		} else if (blocktype.equals("Reference")) {
			for (Node n = node.getFirstChild(); n != null; n = n
					.getNextSibling()) {
				if (n.getNodeType() == Node.ELEMENT_NODE
						&& n.getAttributes().getNamedItem("Name") != null
						&& n.getAttributes().getNamedItem("Name")
								.getNodeValue().equals("const")) {
					blocktype = "Compare to constant";
					return new CompareToConstant(blocktype, blockname, node);
				}
				if (n.getNodeType() == Node.ELEMENT_NODE
						&& n.getAttributes().getNamedItem("Name") != null
						&& n.getAttributes().getNamedItem("Name")
								.getNodeValue().equals("uplimit")) {
					blocktype = "Interval test";
					return new IntervalTest(blocktype, blockname, node);
				}
			}
			blocktype = "Compare to zero";
			return new CompareToZero(blocktype, blockname, node);
		} else if (blocktype.equals("RelationalOperator")) {
			return new RelationalOperator(blocktype, blockname, node);
		} else if (blocktype.equals("Relay")) {
			return new Relay(blocktype, blockname, node);
		} else if (blocktype.equals("Saturate")) {
			return new Saturation(blocktype, blockname, node);
		} else if (blocktype.equals("Scope")) {
			return new Scope(blocktype, blockname, node);
		} else if (blocktype.equals("Signum")) {
			return new Sign(blocktype, blockname, node);
		} else if (blocktype.equals("Sum")) {
			return new Add(blocktype, blockname, node);
		} else if (blocktype.equals("Switch")) {
			return new Switch(blocktype, blockname, node);
		} else if (blocktype.equals("Terminator")) {
			return new Terminator(blocktype, blockname, node);
		} else if (blocktype.equals("UnaryMinus")) {
			return new UnaryMinux(blocktype, blockname, node);
		} else if (blocktype.equals("UnitDelay")) {
			return new UnitDelay(blocktype, blockname, node);
		} else if (blocktype.equals("ZeroOrderHold")) {
			return new ZeroOrderHold(blocktype, blockname, node);
		} else if (blocktype.equals("EnablePort")) {
			return new EnablePort(blocktype, blockname, node);
		} else if (blocktype.equals("TriggerPort")) {
			return new TriggerPort(blocktype, blockname, node);
		} else if (blocktype.equals("Inport")) {
			return new Inport(blocktype, blockname, node, diagLocation);
		} else if (blocktype.equals("Outport")) {
			return new Outport(blocktype, blockname, node, diagLocation);
		} else if (blocktype.equals("SubSystem")) {
			for (Node n = node.getFirstChild(); n != null; n = n
					.getNextSibling()) {
				if (n.getNodeName().equals("System")) {
					SL_Block b = new SubSystem(blocktype, blockname, n,
							diagLocation);
					if (((SubSystem) b).isBroken()) {
						return null;
					} else {
						return b;
					}
				}
			}
			System.out.println("error when translate subsystem" + blockname);
			return new SL_Block(blocktype, blockname);
		} else if (blocktype.equals("userDefinedBlock")) {
			SL_Block b = new UserDefinedBlock("userDefinedBlock", blockname,
					diagLocation);
			if (!((UserDefinedBlock) b).isBroken()) {
				return b;
			} else {
				return null;
			}
		} else if (blocktype.equals("Stateflow")) {
			return new Stateflow(blockname, S2M.getStateflows().get(blockname));
		} else {
			SL_Block b = new UserDefinedBlock("userDefinedBlock", blockname,
					diagLocation);
			if (!((UserDefinedBlock) b).isBroken()) {
				return b;
			} else {
				return null;
			}
		}
	}

	private void analyzeLine(Node node) {  // node == <System><Line>
		SL_Block source = new SL_Block(null, null);
		int srcPort = 0;
		ArrayList<SL_Block> targets = new ArrayList<SL_Block>();
		ArrayList<Integer> dstPorts = new ArrayList<Integer>();
		ArrayList<Node> branches = new ArrayList<Node>();

		for (Node n = node.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n.getNodeType() == Node.ELEMENT_NODE) {
				if (n.getNodeName().equals("Branch")) {
					branches.add(n);
					// continue;
				}
				else if (n.getAttributes().getNamedItem("Name").getNodeValue().equals("SrcBlock")) {
					String src = n.getFirstChild().getNodeValue().replaceAll(" |\n", "");
					source = this.getBlocks().get(src);
				}
				else if (n.getAttributes().getNamedItem("Name").getNodeValue().equals("DstBlock")) {
					String src = n.getFirstChild().getNodeValue().replaceAll(" |\n", "");
					targets.add(this.getBlocks().get(src));
				}
				else if (n.getAttributes().getNamedItem("Name").getNodeValue().equals("SrcPort")) {
					if (!n.getFirstChild().getNodeValue().equals("trigger") && !n.getFirstChild().getNodeValue().equals("enable"))
						srcPort = Integer.parseInt(n.getFirstChild().getNodeValue());
					else
						srcPort = -1;
				}
				else if (n.getAttributes().getNamedItem("Name").getNodeValue().equals("DstPort")) {
					if (!n.getFirstChild().getNodeValue().equals("trigger") && !n.getFirstChild().getNodeValue().equals("enable"))
						dstPorts.add(Integer.parseInt(n.getFirstChild().getNodeValue()));
					else
						dstPorts.add(-1);
				}
			}
		}

		for (int i = 0; i < branches.size(); i++) {
			Node n = branches.get(i);
			for (Node n1 = n.getFirstChild(); n1 != null; n1 = n1
					.getNextSibling()) {
				if (n.getNodeType() != Node.ELEMENT_NODE
						|| n1.getAttributes() == null) {
					continue;
				}
				if (n1.getNodeName().equals("Branch")) {
					branches.add(n1);
					continue;
				}
				if (n1.getAttributes().getNamedItem("Name").getNodeValue()
						.equals("DstBlock")) {
					String src = n1.getFirstChild().getNodeValue()
							.replaceAll(" |\n", "");
					targets.add(this.getBlocks().get(src));
				}
				if (n1.getAttributes().getNamedItem("Name").getNodeValue()
						.equals("DstPort")) {
					if (!n1.getFirstChild().getNodeValue().equals("trigger")
							&& !n1.getFirstChild().getNodeValue()
									.equals("enable"))
						dstPorts.add(Integer.parseInt(n1.getFirstChild()
								.getNodeValue()));
					else
						dstPorts.add(-1);
				}
			}
		}

		if (targets.size() != dstPorts.size())
			System.out.println("wrong in analyzeLine on target list!");
		for (int i = 0; i < targets.size(); i++) {
			SL_Line line = new SL_Line(source, targets.get(i), srcPort,
					dstPorts.get(i), i);
			source.addLine(line, srcPort);
			targets.get(i).addLine(line, dstPorts.get(i));
		}
	}

	// delete a block
	public void deleteBlock(String name) {
		if (this.blocks.containsKey(name)) {
			SL_Block b = this.blocks.get(name);
			for (SL_Line l : b.getDstLines().values()) {
				l.getSource().removeLine(l);
			}
			for (ArrayList<SL_Line> ls : b.getSrcLines().values())
				for (SL_Line l : ls) {
					l.getTarget().removeLine(l);
				}
			this.blocks.remove(name);
		}
	}

	public void addBlock(String name, SL_Block block) {
		if (block != null) {
			blocks.put(name, block);
		}
	}

	public HashMap<String, SL_Block> getBlocks() {
		return blocks;
	}

	public boolean isBroken() {
		return broken;
	}

	// for print
	public void printDiagram(int level) {
		String head = Utilize.tabsAhead(level);
		// print block's info
		for (SL_Block b : blocks.values()) {
			b.printBlock(level);
			System.out.println();
		}
		System.out.println();

		// print lines
		System.out.println(head + "lines:");
		for (SL_Block b : blocks.values()) {
			System.out.println(head + b.getName() + ":");
			b.printLines(level);
		}
	}

	public void printStateflow() {
		for (SL_Block b : blocks.values()) {
			if (b.getType().equals("Stateflow")) {
				((Stateflow) b).print();
				System.out.println();
			}
		}
	}

}
