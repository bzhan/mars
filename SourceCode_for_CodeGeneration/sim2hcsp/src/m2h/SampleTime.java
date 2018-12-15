package m2h;

import java.util.ArrayList;

import model.SL_Diagram;
import model.SL_Block;
import model.SL_Line;
import model.subsystems.SubSystem;

public class SampleTime {

	protected static boolean calSampleTime(SL_Diagram diagram) {

		// sample time for trigger and enable subsystem is its control signal
		for (SL_Block b1 : diagram.getBlocks().values()) {
			if (b1.getType().equals("SubSystem")) {
				for (SL_Line l : b1.getDstLines().values()) {
					if (l.getDstPort() == -1) {
						b1.getParameters().put("st",
								l.getSource().getParameters().get("st"));
					}
				}
			}
		}

		boolean loopFlag = true;
		while (loopFlag) {
			loopFlag = false;
			for (SL_Block b : diagram.getBlocks().values()) {
				if (!b.getParameters().get("st").equals("-1")) {
					continue;
				}

				boolean decidableFlag = true;
				ArrayList<String> stLists = new ArrayList<String>();
				for (SL_Line l : b.getDstLines().values()) {
					if (l.getDstPort() == -1)
						continue;
					if (l.getSource().getParameters().get("st").equals("-1")) {
						decidableFlag = false;
						break;
					} else {
						stLists.add(l.getSource().getParameters().get("st"));
					}
				}
				if (decidableFlag) {
					loopFlag = true;
					if (!b.getType().equals("SubSystem"))
						b.getParameters().put("st", GCD(stLists));
					if (b.getType().equals("SubSystem")
							&& (((SubSystem) b).getSystemType().equals(
									"Trigger") || ((SubSystem) b)
									.getSystemType().equals("Enable"))) {
						if (isAllEqual(stLists)) {
							b.getParameters().put("st", stLists.get(0));
						} else {
							System.out
									.println("Inputs for triggered or enabled subsystem "
											+ "donot have the same sample time!");
							b.getParameters().put("st", GCD(stLists));
						}
					} else if (b.getType().equals("SubSystem")) {
						System.out.println("Normal subsystem still exists!");
						return false;
					}

				}
			}
		}

		for (SL_Block b : diagram.getBlocks().values()) {
			if (b.getParameters().get("st").equals("-1")) {
				System.out.println("sample time for block " + b.getName()
						+ " is not decidable!");
				return false;
			}
		}
		return true;
	}

	protected static boolean isAllEqual(ArrayList<String> stLists) {
		// calculate the biggest times of moving the points
		//System.out.print("@@@@@@@@"+stLists+"@@@@@@@@@");
		int biggestTimes = 0;//for 0.1 0.01 0.001,biggestTimes=3  
		for (String str : stLists) {
			if (!str.equals("inf") && str.indexOf(".") >= 0) {
				biggestTimes = Math.max(biggestTimes,
						str.length() - str.indexOf(".") - 1);
			}
		}
		// transform all sample times to integers by moving the points
		ArrayList<Long> longSTs = new ArrayList<Long>();
		for (String str : stLists) {//0.1 changed to 0100, 0.01 to 0010, 0.001 to 0001
			if (!str.equals("inf")) {
				String finalStr = str.replace(".", "");
				for (int j = 0; j < biggestTimes
						- (str.length() - str.indexOf(".") - 1); j++) {
					finalStr += '0';
				}
				longSTs.add(Long.parseLong(finalStr));
			}
		}

		for (long n : longSTs) {// any two number do not equal, return false
			if (n != longSTs.get(0))
				return false;
		}
		return true;

		// if (longSTs.isEmpty()) {
		// return true;
		// } else if (longSTs.size() == stLists.size()) {
		// for (long n : longSTs) {
		// if (n != longSTs.get(0))
		// return false;
		// }
		// return true;
		// } else {
		// return false;
		// }
	}

	protected static String GCD(ArrayList<String> stLists) {

		// calculate the biggest times of moving the points
		int biggestTimes = 0;
		for (String str : stLists) {
			if (!str.equals("inf") && str.indexOf(".") >= 0) {
				biggestTimes = Math.max(biggestTimes,
						str.length() - str.indexOf(".") - 1);
			}
		}

		// transform all sample times to integers by moving the points
		ArrayList<Long> longSTs = new ArrayList<Long>();
		for (String str : stLists) {
			if (!str.equals("inf")) {
				String finalStr = str.replace(".", "");
				if (str.indexOf(".") == -1) {
					for (int j = 0; j < biggestTimes; j++) {
						finalStr += '0';
					}
				} else {
					for (int j = 0; j < biggestTimes
							- (str.length() - str.indexOf(".") - 1); j++) {
						finalStr += '0';
					}
				}
				longSTs.add(Long.parseLong(finalStr.replace(" ", "")));
			}
		}

		// if exist a 0 in the list, return 0
		for (long n : longSTs) {
			if (n == 0) {
				return "0";
			}
		}

		// calculate the GCD of the integers and translate it to string
		if (longSTs.size() == 0) {
			return "inf";
		}
		long longResult = longSTs.get(0);
		for (long l : longSTs) {
			longResult = fGCD(longResult, l);
		}
		String longStringResult = Long.toString(longResult);

		// moving the point back
		String doubleStringResult;
		if (biggestTimes == 0) {
			doubleStringResult = longStringResult;
		} else if (longStringResult.length() > biggestTimes) {
			doubleStringResult = longStringResult.substring(0,
					longStringResult.length() - biggestTimes)
					+ '.'
					+ longStringResult.substring(longStringResult.length()
							- biggestTimes, longStringResult.length());
		} else {
			doubleStringResult = "0.";
			for (int j = 0; j < biggestTimes - longStringResult.length(); j++) {
				doubleStringResult += '0';
			}
			doubleStringResult += longStringResult;
		}

		return doubleStringResult;
	}

	private static long fGCD(long a, long b) {
		if (a == 0) {
			return b;
		} else if (b == 0) {
			return a;
		} else if (a < b) {
			return fGCD(a, b % a);
		} else {
			return fGCD(a % b, b);
		}
	}
}
