package m2h;

import java.util.ArrayList;

import model.SL_Block;
import model.SL_Diagram;

public class Optimization {

	// delete useless blocks
	protected static void deleteUselessBlocks(SL_Diagram diagram) {
		ArrayList<String> names = new ArrayList<String>();
		for (SL_Block b : diagram.getBlocks().values()) {
			if (b.getType().equals("Scope") || b.getType().equals("Display")
					|| b.getType().equals("Terminator")) {
				names.add(b.getName());
			}
		}
		for (String name : names) {
			diagram.deleteBlock(name);
		}
	}

	// make the semantics function of constant empty, and replace that variable
	// to value.
	protected static String deleteConstantVariable(SL_Diagram diagram,
			String process) {
		for (SL_Block b : diagram.getBlocks().values()) {
			if (b.getType().equals("Constant")) {
				process = process.replaceAll(b.getSrcLines().get(1).get(0)
						.getVarName().replaceAll("\\_", "\\_"), "(Real "
						+ b.getParameters().get("val").replaceAll("-", "--")
						+ ")");
			}
		}
		return process;
	}
}
