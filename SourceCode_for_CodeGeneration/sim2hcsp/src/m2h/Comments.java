package m2h;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class Comments {
	
	protected static void commentsPrint() {
		System.out.println("\nComments:");
		InputStream inputstream;
		try {
			inputstream = new FileInputStream(SL2HCSP.getUdsLocation() + "comments");
			BufferedReader bufferreader = new BufferedReader(new InputStreamReader(inputstream));

			// analyze the file.
			for (String l1 = bufferreader.readLine(); l1 != null; l1 = bufferreader.readLine()) {
				System.out.println(l1);
			}
			inputstream.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}

	}
	
}
