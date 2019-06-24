package model;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class S2M {
	private static HashMap<String, Node> stateflows = new HashMap<String, Node>();

	public static SL_Diagram s2m(String xmlLocation) {
		DocumentBuilderFactory domfac = DocumentBuilderFactory.newInstance();

		DocumentBuilder dombuilder;
		try {
			dombuilder = domfac.newDocumentBuilder();
			//File file = new File(xmlLocation);
			//System.out.println(file.exists());
			//System.out.println(xmlLocation);
			InputStream xml = new FileInputStream(xmlLocation);
			Document doc = dombuilder.parse(xml);

			NodeList root = doc.getElementsByTagName("System");
			if (root == null) {
				System.out
						.println("No Simulink model is contained in XML file!!!");
				return null;
			}

			// find out all Stateflow charts
			NodeList charts = doc.getElementsByTagName("chart");
			for (int i = 0; i < charts.getLength(); i++) {
				String name = "";
				for (int j = 0; j < charts.item(i).getChildNodes().getLength(); j++) {
					Node node = charts.item(i).getChildNodes().item(j);
					if (node.getAttributes() != null
							&& node.getAttributes().getNamedItem("Name") != null
							&& node.getAttributes().getNamedItem("Name").getNodeValue().equals("name")) {
						name = node.getFirstChild().getNodeValue();
						// break?
						break;
					}
				}
				stateflows.put(name, charts.item(i));
			}

			return new SL_Diagram(root.item(0), ""); // (<System>, "")
		} catch (ParserConfigurationException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	public static HashMap<String, Node> getStateflows() {
		return S2M.stateflows;
	}
}
