package m2h;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;

import model.SL_Block;
import model.SL_Diagram;
import model.SL_Line;

public class Partition {

	protected static ArrayList<ArrayList<String>> partition(SL_Diagram diagram) {

		ArrayList<ArrayList<String>> partition = new ArrayList<ArrayList<String>>();

		// It is handled by add rules for isCommLine. *any triggered or enabled
		// subsystem is a partition*
		// for (SL_Block b : diagram.getBlocks().values()) {
		// if (b.getType().equals("SubSystem")
		// && (((SubSystem) b).getSystemType().equals("Trigger") || ((SubSystem)
		// b)
		// .getSystemType().equals("Enable"))) {
		// ArrayList<String> scc = new ArrayList<String>();
		// scc.add(b.getName());
		// partition.add(scc);
		// }
		// }

		// get user defined connections
		HashMap<String, ArrayList<String>> map = addConnPartition();

		// get the partition
		for (SL_Block b : diagram.getBlocks().values()) {
			if (b.getParameters().containsKey("bfs")) {
				continue;
			}

			ArrayList<String> scc = new ArrayList<String>();
			scc.add(b.getName());
			b.getParameters().put("bfs", "t");

			ArrayList<SL_Block> bs = new ArrayList<SL_Block>();
			bs.add(b);
			while (!bs.isEmpty()) {
				if (map.get(bs.get(0).getName()) != null) {
					for (String str : map.get(bs.get(0).getName())) {
						if (scc.contains(str)) {
							continue;
						}
						bs.add(diagram.getBlocks().get(str));
						scc.add(str);
						diagram.getBlocks().get(str).getParameters()
								.put("bfs", "t");
					}
				}
				for (SL_Line l : bs.get(0).getDstLines().values()) {
					if (Comms.isCommLine(l))
						continue;
					if (scc.contains(l.getSource().getName()))
						continue;
					bs.add(l.getSource());
					scc.add(l.getSource().getName());
					l.getSource().getParameters().put("bfs", "t");
				}
				for (ArrayList<SL_Line> ls : bs.get(0).getSrcLines().values()) {
					for (SL_Line l : ls) {
						if (Comms.isCommLine(l))
							continue;
						if (scc.contains(l.getTarget().getName()))
							continue;
						bs.add(l.getTarget());
						scc.add(l.getTarget().getName());
						l.getTarget().getParameters().put("bfs", "t");
					}
				}
				bs.remove(0);
			}
			partition.add(scc);
		}

		// delete the parameter bfs
		for (SL_Block b : diagram.getBlocks().values()) {
			b.getParameters().remove("bfs");
		}

		// modify target partition for all lines
		for (int i = 0; i < partition.size(); i++) {
			ArrayList<String> apar = partition.get(i);
			for (String bstr : apar) {
				SL_Block b = diagram.getBlocks().get(bstr);
				for (SL_Line l : b.getDstLines().values()) {
					l.setPartition(i);
				}
			}
		}
		return partition;
	}

	protected static HashMap<String, ArrayList<String>> addConnPartition() {
		HashMap<String, ArrayList<String>> map = new HashMap<String, ArrayList<String>>();
		// user defined connections
		InputStream inputstream;
		try {
			inputstream = new FileInputStream(SL2HCSP.getUdsLocation()
					+ "connections");
			BufferedReader bufferreader = new BufferedReader(
					new InputStreamReader(inputstream));

			// analyze the file.
			for (String l1 = bufferreader.readLine(); l1 != null; l1 = bufferreader
					.readLine()) {
				if (l1.indexOf(";") > 0) {
					String c1 = l1.substring(0, l1.indexOf(";")).replaceAll(
							" ", "");
					String c2 = l1.substring(l1.indexOf(";") + 1, l1.length())
							.replaceAll(" ", "");
					if (map.containsKey(c1)) {
						map.get(c1).add(c2);
					} else {
						ArrayList<String> list = new ArrayList<String>();
						list.add(c2);
						map.put(c1, list);
					}
					if (map.containsKey(c2)) {
						map.get(c2).add(c1);
					} else {
						ArrayList<String> list = new ArrayList<String>();
						list.add(c1);
						map.put(c2, list);
					}
				} else if (l1.replaceAll(" ", "").equals("")) {
					continue;
				} else {
					System.out
							.println("User defined connections: Syntax error.");
				}
			}
			inputstream.close();
		} catch (FileNotFoundException e) {
			// System.out.println("File commLines is not found!");
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
		return map;
	}

	// for print
	protected static void printPartition(ArrayList<ArrayList<String>> partition) {
		for (ArrayList<String> aPartition : partition) {
			System.out.print("scc:");
			for (String str : aPartition) {
				System.out.println("\t" + str);
			}
		}
	}

}
