package m2h;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;

import model.SL_Block;
import model.SL_Diagram;
import model.SL_Line;
import model.subsystems.SubSystem;

public class Comms {

	protected static String dealWithComms(SL_Diagram diagram) {
		ArrayList<SL_Line> commLine = Comms.getCommLine(diagram);
		ArrayList<String> comms = new ArrayList<String>();
		String buf = "";
		for (SL_Line l : commLine) {
			// ignore when l has already sent to the partition
			if (comms.contains(l.getChName())) {
				continue;
			} else {
				comms.add(l.getChName());
			}

			// from continuous to discrete
			if (l.getSource().getParameters().get("st").equals("0")
					&& !l.getSource().getParameters().keySet()
							.contains("discrete")
					&& (!l.getTarget().getParameters().get("st").equals("0") || l
							.getTarget().getParameters().keySet()
							.contains("discrete"))) {
				// continuous source
				if (l.getSource().getParameters().get("comm") == null) {
					l.getSource()
							.getParameters()
							.put("comm",
									"Ch_" + l.getChName() + "!"
											+ l.getVarName());
				} else {
					String str = l.getSource().getParameters().get("comm")
							+ "\n [] Ch_" + l.getChName() + "!"
							+ l.getVarName();
					l.getSource().getParameters().put("comm", str);
				}
				// discrete target
				if (l.getTarget().getParameters().get("commIn") == null) {
					l.getTarget()
							.getParameters()
							.put("commIn",
									"Ch_" + l.getChName() + "?" + l.getChName());
				} else {
					String str = l.getTarget().getParameters().get("commIn")
							+ ";\n Ch_" + l.getChName() + "?" + l.getChName();
					l.getTarget().getParameters().put("commIn", str);
				}
			}

			// from discrete to continuous
			else if ((!l.getSource().getParameters().get("st").equals("0") || l
					.getSource().getParameters().keySet().contains("discrete"))
					&& l.getTarget().getParameters().get("st").equals("0")
					&& !l.getTarget().getParameters().keySet()
							.contains("discrete")) {
				// discrete source
				if (l.getSource().getParameters().get("commOut") == null) {
					l.getSource()
							.getParameters()
							.put("commOut",
									"Ch_" + l.getChName() + "!"
											+ l.getVarName());
				} else {
					String str = l.getSource().getParameters().get("commOut")
							+ ";\n Ch_" + l.getChName() + "!" + l.getVarName();
					l.getSource().getParameters().put("commOut", str);
				}
				// continuous target
				if (l.getTarget().getParameters().get("comm") == null) {
					l.getTarget()
							.getParameters()
							.put("comm",
									"Ch_" + l.getChName() + "?" + l.getChName());
				} else {
					String str = l.getTarget().getParameters().get("comm")
							+ "\n [] Ch_" + l.getChName() + "?" + l.getChName();
					l.getTarget().getParameters().put("comm", str);
				}
			}

			// from discrete to discrete
			else if ((!l.getSource().getParameters().get("st").equals("0") || l
					.getSource().getParameters().keySet().contains("discrete"))
					&& (!l.getTarget().getParameters().get("st").equals("0") || l
							.getTarget().getParameters().keySet()
							.contains("discrete"))) {
				// discrete source
				if (l.getSource().getParameters().get("commOut") == null) {
					l.getSource()
							.getParameters()
							.put("commOut",
									"Cbi_" + l.getChName() + "!"
											+ l.getVarName());
				} else {
					String str = l.getSource().getParameters().get("commOut")
							+ ";\n Cbi_" + l.getChName() + "!" + l.getVarName();
					l.getSource().getParameters().put("commOut", str);
				}
				// discrete target
				if (l.getTarget().getParameters().get("commIn") == null) {
					l.getTarget()
							.getParameters()
							.put("commIn",
									"Cbo_" + l.getChName() + "?"
											+ l.getChName());
				} else {
					String str = l.getTarget().getParameters().get("commIn")
							+ ";\n Cbo_" + l.getChName() + "?" + l.getChName();
					l.getTarget().getParameters().put("commIn", str);
				}
				if (!buf.equals(""))
					buf += " ||\n";
				buf += "fbuf(Cbi_" + l.getChName() + "?b" + l.getVarName()
						+ "," + "Cbo_" + l.getChName() + "!b" + l.getVarName()
						+ "," + l.getSource().getParameters().get("st") + ","
						+ l.getTarget().getParameters().get("st") + ")";
			}
		}
		return buf;
	}

	// get all communication lines by using the function "isCommLine" in the
	// following.
	protected static ArrayList<SL_Line> getCommLine(SL_Diagram diagram) {
		ArrayList<SL_Line> commLine = new ArrayList<SL_Line>();
		for (SL_Block b : diagram.getBlocks().values()) {
			for (ArrayList<SL_Line> ls : b.getSrcLines().values()) {
				for (SL_Line l : ls) {
					if (isCommLine(l)) {
						commLine.add(l);
					}
				}
			}
		}
		// printCommLine(commLine);
		return commLine;
	}

	@SuppressWarnings("unused")
	private static void printCommLine(ArrayList<SL_Line> commLine) {
		if (commLine.isEmpty())
			System.out.println("CommLines:\t" + "null");
		else
			System.out.print("CommLines:");
		for (SL_Line l : commLine) {
			l.printLine(0);
		}
		System.out.println();
	}

	public static boolean isCommLine(SL_Line line) {

		// all lines connected to a triggered subsystem is comm lines
		if ((line.getSource().getType().equals("SubSystem") && ((SubSystem) line
				.getSource()).getSystemType().equals("Trigger"))
				|| (line.getTarget().getType().equals("SubSystem") && ((SubSystem) line
						.getTarget()).getSystemType().equals("Trigger"))
				|| (line.getSource().getType().equals("Stateflow"))
				|| (line.getTarget().getType().equals("Stateflow"))) {
			return true;
		}

		// user defined comm Lines
		InputStream inputstream;
		try {
			inputstream = new FileInputStream(SL2HCSP.getUdsLocation()
					+ "commLines");
			@SuppressWarnings("resource")
			BufferedReader bufferreader = new BufferedReader(
					new InputStreamReader(inputstream));

			// analyze the file.
			for (String l1 = bufferreader.readLine(); l1 != null; l1 = bufferreader
					.readLine()) {
				if (l1.indexOf(";") > 0) {
					String sourcePair = l1.substring(0, l1.indexOf(";"));
					String targetPair = l1.substring(l1.indexOf(";") + 1,
							l1.length());
					if (sourcePair.indexOf(",") > 0
							&& targetPair.indexOf(",") > 0) {
						String source = sourcePair.substring(0,
								sourcePair.indexOf(",")).replaceAll(" ", "");
						String target = targetPair.substring(0,
								targetPair.indexOf(",")).replaceAll(" ", "");
						int sourcePort = Integer.parseInt(sourcePair.substring(
								sourcePair.indexOf(",") + 1,
								sourcePair.length()).replaceAll(" ", ""));
						int targetPort = Integer.parseInt(targetPair.substring(
								targetPair.indexOf(",") + 1,
								targetPair.length()).replaceAll(" ", ""));
						if (line.getSource().getName().equals(source)
								&& line.getSrcPort() == sourcePort
								&& line.getTarget().getName().equals(target)
								&& line.getDstPort() == targetPort) {
							return true;
						}
					} else if (l1.replaceAll(" ", "").equals("")) {
						continue;
					} else {
						System.out
								.println("User defined communication lines: Syntax error.");
					}
				} else if (l1.replaceAll(" ", "").equals("")) {
					continue;
				} else {
					System.out
							.println("User defined communication lines: Syntax error.");
				}
			}
			bufferreader.close();
			inputstream.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// from discrete to continuous or from continuous to discrete.
		if (line.getSource().getParameters().containsKey("st")
				&& line.getTarget().getParameters().containsKey("st")) {
			if (line.getSource().getParameters().get("st").equals("inf")
					|| line.getTarget().getParameters().get("st").equals("inf"))
				return false;
			else if (((!line.getSource().getParameters().get("st").equals("0") || line
					.getSource().getParameters().keySet().contains("discrete"))
					&& line.getTarget().getParameters().get("st").equals("0") && !line
					.getTarget().getParameters().keySet().contains("discrete"))
					|| (line.getSource().getParameters().get("st").equals("0")
							&& !line.getSource().getParameters().keySet()
									.contains("discrete") && (!line.getTarget()
							.getParameters().get("st").equals("0") || line
							.getTarget().getParameters().keySet()
							.contains("discrete")))) {
				return true;
			}
		} else {
			System.out.println("Some block do not have sample time!!!");
		}
		return false;
	}
}
