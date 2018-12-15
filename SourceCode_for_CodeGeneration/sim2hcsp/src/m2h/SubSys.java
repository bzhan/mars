package m2h;

import java.util.ArrayList;
import java.util.HashMap;

import model.SL_Diagram;
import model.SL_Block;
import model.SL_Line;
import model.subsystems.SubSystem;
import model.subsystems.Inport;

public class SubSys {
	protected static void deleteNomalSubSys(SL_Diagram diagram) {

		// the added blocks
		SL_Diagram subDiagram = new SL_Diagram();
		// deleted subsystem blocks
		ArrayList<String> delSys = new ArrayList<String>();

		for (SL_Block b : diagram.getBlocks().values()) {
			if (b.getType().equals("SubSystem") && ((SubSystem) b).getSystemType().equals("Normal")) {
				String name = b.getName();
				delSys.add(name);
				for (SL_Block b1 : ((SubSystem) b).getSubDiagram().getBlocks().values()) {
					if (b1.getType().equals("Inport")) {
						int port = Integer.parseInt(b1.getParameters().get("Port"));
						SL_Block source = b.getDstLine(port).getSource();
						int srcPort = b.getDstLine(port).getSrcPort();
						int branch = b.getDstLine(port).getBranch();
						ArrayList<SL_Line> srcLines = source.getSrcLine(srcPort);
						srcLines.remove(branch);
						for (int i = 0; i < b1.getSrcLine(1).size(); i++) {
							SL_Line l = b1.getSrcLine(1).get(i);
							SL_Block target = l.getTarget();
							int dstPort = l.getDstPort();
							SL_Line line = new SL_Line(source, target, srcPort, dstPort, branch + i);
							l.getTarget().getDstLines().put(dstPort, line);
							srcLines.add(branch + i, line);
						}
						// repair the branches
						for (int i = 0; i < srcLines.size(); i++) {
							srcLines.get(i).setBranch(i);
						}
						source.getSrcLines().put(srcPort, srcLines);
					} else if (b1.getType().equals("Outport")) {
						int port = Integer.parseInt(b1.getParameters().get("Port"));
						SL_Block source = b1.getDstLine(1).getSource();
						int srcPort = b1.getDstLine(1).getSrcPort();
						int branch = b1.getDstLine(1).getBranch();
						ArrayList<SL_Line> srcLines = source.getSrcLine(srcPort);
						srcLines.remove(branch);
						for (int i = 0; i < b.getSrcLine(port).size(); i++) {
							SL_Line l = b.getSrcLine(port).get(i);
							SL_Block target = l.getTarget();
							int dstPort = l.getDstPort();
							SL_Line line = new SL_Line(source, target, srcPort, dstPort, branch + i);
							l.getTarget().getDstLines().put(dstPort, line);
							srcLines.add(branch + i, line);
						}
						// repair the branches
						for (int i = 0; i < srcLines.size(); i++) {
							srcLines.get(i).setBranch(i);
						}
						source.getSrcLines().put(srcPort, srcLines);
					} else {
						b1.setName(name + "_" + b1.getName());
						subDiagram.addBlock(b1.getName(), b1);
					}
				}
			}
		}

		for (SL_Block b : subDiagram.getBlocks().values()) {
			diagram.addBlock(b.getName(), b);
		}
		for (String str : delSys) {
			diagram.getBlocks().remove(str);
		}
	}

	protected static void triggeredSubSys(SL_Diagram diagram) {

		for (SL_Block b1 : diagram.getBlocks().values()) {
			if (b1.getType().equals("SubSystem")
					&& ((SubSystem) b1).getSystemType().equals("Trigger")) {
				setFunTri(b1, ((SubSystem) b1).getSubDiagram());
			}
		}

	}

	private static void setFunTri(SL_Block b, SL_Diagram diagram) {
		// change the name of block in subsystem
		SL_Diagram subDiagram = new SL_Diagram();
		for (SL_Block b1 : diagram.getBlocks().values()) {
			if (!b1.getType().equals("TriggerPort")) {
				b1.setName(b.getName() + "_" + b1.getName());
				subDiagram.addBlock(b1.getName(), b1);
			}
		}

		// set sample time of triggered subsystem to 1, and set all sample time
		// of all blocks in it to 1
		for (SL_Block b1 : subDiagram.getBlocks().values()) {
			b1.getParameters().put("st", "1");
		}

		// set in-port variable name for in-ports
		HashMap<Integer, String> inVarNames = b.getinVarNames();
		for (SL_Block b1 : subDiagram.getBlocks().values()) {
			if (b1.getType().equals("Inport")) {
				int port = Integer.parseInt(((Inport) b1).getParameters().get("Port"));
				((Inport) b1).setInVarName(inVarNames.get(port));
			}
		}

		// the all blocks form a partition
		ArrayList<String> aPartition = new ArrayList<String>();
		for (SL_Block b1 : subDiagram.getBlocks().values()) {
			aPartition.add(b1.getName());
		}

		// reorder the partition
		ArrayList<String> thePartition = new ArrayList<String>();
		Boolean loopFlag;
		Boolean freeFlag;
		do {
			loopFlag = false;
			for (String str : aPartition) {
				freeFlag = true;
				for (SL_Line l : subDiagram.getBlocks().get(str).getDstLines().values()) {
					if (aPartition.contains(l.getSource().getName())) {
						freeFlag = false;
						break;
					}
				}
				if (freeFlag) {
					thePartition.add(str);
					aPartition.remove(str);
					loopFlag = true;
					break;
				}
			}
		} while (loopFlag);

		// initialization
		String init = "";
		for (String str : thePartition) {
			SL_Block b1 = subDiagram.getBlocks().get(str);
			if (b1.semanticFunctionDiscrete().get("init") != null
					&& !b1.semanticFunctionDiscrete().get("init").replaceAll(" ", "").equals("")) {
				init += b1.semanticFunctionDiscrete().get("init") + ";\n";
			}
		}

		// computation
		String comp = "";
		for (String str : thePartition) {
			SL_Block b1 = subDiagram.getBlocks().get(str);
			comp += b1.semanticFunctionDiscrete().get("fun") + ";\n";
		}
		comp = comp.replaceAll("null;", "");
		comp = comp.replaceAll("\n\n", "\n");

		// trigger channel
		String triCh = "";
		for (SL_Line l : b.getDstLines().values()) {
			if (l.getDstPort() == -1) {
				triCh = l.getChName();
				triCh = triCh.replaceAll("-1", "t");
			}
		}

		// get communications
		String commInStr = "";
		String commOutStr = "";
		if (b.getParameters().get("commIn") != null) {
			commInStr += b.getParameters().get("commIn") + ";\n";
		}
		if (b.getParameters().get("commOut") != null) {
			commOutStr += b.getParameters().get("commOut") + ";\n";
		}

		// return a process
		String process = init + "(" + triCh + "?" + commInStr + comp + commOutStr + ")*";

		((SubSystem) b).setProcess(process);

	}

	protected static void enableSubSys(SL_Diagram diagram) {

		for (SL_Block b1 : diagram.getBlocks().values()) {
			if (b1.getType().equals("SubSystem")
					&& ((SubSystem) b1).getSystemType().equals("Enable")) {
				treatEnableSusSys(b1, ((SubSystem) b1).getSubDiagram());
			}
		}
	}

	private static void treatEnableSusSys(SL_Block b, SL_Diagram diagram) {
		// change the name of block in subsystem
		SL_Diagram subDiagram = new SL_Diagram();
		for (SL_Block b1 : diagram.getBlocks().values()) {
			if (!b1.getType().equals("EnablePort")) {
				b1.setName(b.getName() + "_" + b1.getName());
				subDiagram.addBlock(b1.getName(), b1);
			}
		}

		// enable variable and its sample time
		// String enVar = "";
		String st = "";
		for (SL_Line l : b.getDstLines().values()) {
			if (l.getDstPort() == -1) {
				// enVar = l.getVarName();
				st = l.getSource().getParameters().get("st");
			}
		}

		// solve all sample times of enabled subsystem
		for (SL_Block b1 : subDiagram.getBlocks().values()) {
			b1.getParameters().put("st", st);
		}

		// set in-port variable name for in-ports
		HashMap<Integer, String> inVarNames = b.getinVarNames();
		for (SL_Block b1 : subDiagram.getBlocks().values()) {
			if (b1.getType().equals("Inport")) {
				int port = Integer.parseInt(((Inport) b1).getParameters().get("Port"));
				((Inport) b1).setInVarName(inVarNames.get(port));
			}
		}

		// the all blocks form a partition
		ArrayList<String> aPartition = new ArrayList<String>();
		for (SL_Block b1 : subDiagram.getBlocks().values()) {
			aPartition.add(b1.getName());
		}

		// initialization
		String init = "";
		for (String str : aPartition) {
			SL_Block b1 = subDiagram.getBlocks().get(str);
			if (b1.semanticFunctionDiscrete().get("init") != null
					&& !b1.semanticFunctionDiscrete().get("init").replaceAll(" ", "").equals("")) {
				init += b1.semanticFunctionDiscrete().get("init") + ";\n";
			}
		}

		HashMap<String, String> semantics = new HashMap<String, String>();
		if (st.replaceAll(" ", "").equals("0")) {
		} else {
			// reorder the partition
			ArrayList<String> thePartition = new ArrayList<String>();
			Boolean loopFlag;
			Boolean freeFlag;
			do {
				loopFlag = false;
				for (String str : aPartition) {
					freeFlag = true;
					for (SL_Line l : subDiagram.getBlocks().get(str).getDstLines().values()) {
						if (aPartition.contains(l.getSource().getName())) {
							freeFlag = false;
							break;
						}
					}
					if (freeFlag) {
						thePartition.add(str);
						aPartition.remove(str);
						loopFlag = true;
						break;
					}
				}
			} while (loopFlag);

			// computation
			String comp = "";
			for (String str : thePartition) {
				SL_Block b1 = subDiagram.getBlocks().get(str);
				comp += b1.semanticFunctionDiscrete().get("fun") + ";\n";
			}
			comp = comp.replaceAll("null;", "");
			comp = comp.replaceAll("\n\n", "\n");

			semantics.put("init", init);
			semantics.put("fun", comp);
			((SubSystem) b).setSemantics(semantics);
		}

	}
}
