package model;

public class Utilize {
	public static String tabsAhead (int level) {
		String head = "";
		for (int i = 0; i<level; i++) {
			head += "\t";
		}
		return head;
	}

}
