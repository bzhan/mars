package model.userDefinedBlocks;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;

import m2h.SL2HCSP;
import model.SL_Block;

public class UserDefinedBlock extends SL_Block {
	private HashMap<String, String> semanticsMap = new HashMap<String, String>();
	// private String semanticsType;
	private boolean broken;

	public UserDefinedBlock(String blockType, String blockName,
			String diagLocation) {
		super(blockType, blockName);
		broken = false;
		anylyzeFile(SL2HCSP.getUdsLocation() + diagLocation + blockName);

		if (semanticsMap.containsKey("st")) {
			super.getParameters().put("st", semanticsMap.get("st").replace(" ", ""));
			semanticsMap.remove("st");
		} else {
			super.getParameters().put("st", "-1");
		}
	}

	public void anylyzeFile(String path) {

		InputStream inputstream;
		try {
			inputstream = new FileInputStream(path);
			BufferedReader bufferreader = new BufferedReader(new InputStreamReader(inputstream));

			// analyze the file.
			ArrayList<Boolean> outTypes = new ArrayList<Boolean>();
			for (String line = bufferreader.readLine(); line != null; line = bufferreader
					.readLine()) {
				if (line.indexOf(":") > 0) {
					String name = line.substring(0, line.indexOf(":")).replaceAll(" ", "");
					String item = line.substring(line.indexOf(":") + 1, line.length());
					if (name.equals("type")) {
						outTypes.add(Boolean.valueOf(item.replaceAll(" ", "")));
					} else
						semanticsMap.put(name, item);
				} else if (line.replaceAll(" ", "").equals("")) {
					continue;
				} else {
					System.out.println("File " + path + ": Syntax error.");
					semanticsMap.clear();
					broken = true;
				}
			}
			super.setOutTypes(outTypes);
			inputstream.close();
		} catch (FileNotFoundException e) {
			System.out.println("File " + path + " is not found!");
			broken = true;
			// e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			broken = true;
			e.printStackTrace();
		}
	}

	public HashMap<String, String> semanticFunctionContinuous() {
		return semanticsMap;
	}

	public HashMap<String, String> semanticFunctionDiscrete() {
		return semanticsMap;
	}

	public boolean isBroken() {
		return broken;
	}

}
