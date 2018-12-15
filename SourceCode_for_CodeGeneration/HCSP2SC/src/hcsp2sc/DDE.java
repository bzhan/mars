package hcsp2sc;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;

public class DDE {//the DDE object 
	public String ddeString; //dde string
	public String ddeName=""; //dde string
	public String simResultAddr;//address of the simulation result
	public float L;
	public float Epoint;
	public float Etime;
	
	public DDE (String dde)
	{
		ddeString = dde;
	}
	public ArrayList<String> getTimes(){ //get the time sequence from the simulation result file 'simResultAddr'
		ArrayList<String> times= new ArrayList<String>();
		try {
			BufferedReader input=new BufferedReader(new FileReader(simResultAddr));
			String data="",resultString="";
			while((data=input.readLine())!=null) //get the content as a string
			{
				resultString+=data;
			}
			String timesSeq=resultString.substring(resultString.indexOf("times=")+6, resultString.indexOf(",;"));//get the 'times' string			
			String[] timevalues=timesSeq.split(","); //split the result
			for(int i=0;i<timevalues.length;i++) // store the result into the list
			{
				times.add(timevalues[i]);
			}
			//System.out.println(timesSeq);
			input.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return times;		
	}
	public ArrayList<String> getValues(){//get the state sequence from the simulation result file 'simResultAddr'
		ArrayList<String> values= new ArrayList<String>();
		try {
			BufferedReader input=new BufferedReader(new FileReader(simResultAddr));
			String data="",resultString="";
			while((data=input.readLine())!=null)
			{
				resultString+=data;
			}
			String[] valuesV=null;
			if(ddeName.length()==0||ddeName.isEmpty()||ddeName.equals("")) //only one dde
			{
				if(resultString.indexOf("),;errors=")>0)//for dim>1
				{
					String valuesSeq=resultString.substring(resultString.indexOf("values=(")+8, resultString.indexOf("),;errors="));			
					valuesV=valuesSeq.split("\\),\\(");
				}
				else //for dim=1
				{
					String valuesSeq=resultString.substring(resultString.indexOf("values=")+7, resultString.indexOf(",;errors="));			
					valuesV=valuesSeq.split(",");
				}
			}
			else //more than one ddes
			{
				String[] temp_ddes=resultString.split(",;values_");
				for (int i=1;i<temp_ddes.length;i++)
				{
					if(temp_ddes[i].contains(ddeName))
					{
						String temp="";
						if(i==temp_ddes.length-1)
						{
							temp=temp_ddes[i].substring(temp_ddes[i].indexOf(ddeName+"=")+ddeName.length()+1,temp_ddes[i].lastIndexOf(","));
						}
						else
						{
							temp=temp_ddes[i].substring(temp_ddes[i].indexOf(ddeName+"=")+ddeName.length()+1);

						}
						if(temp.contains("\\),\\("))
						{
							String temp_1=temp.substring(temp.indexOf("\\(")+1, temp.lastIndexOf("\\)"));
							valuesV=temp_1.split("\\),\\(");
						}
						else
						{
							valuesV=temp.split(",");
						}						
					}
				}
/*			    if(resultString.lastIndexOf("),;values_")>0)//for dim>1
			    {
				    String valuesSeq=resultString.substring(resultString.indexOf("values_"+ddeName+"=(")+9+ddeName.length(), resultString.indexOf("),;values_",resultString.indexOf("values_"+ddeName+"=(")+9+ddeName.length()));			
				    valuesV=valuesSeq.split("\\),\\(");
			    }
			    else if  (resultString.lastIndexOf(",;values_")>0)//for dim=1
			    {
				    String valuesSeq=resultString.substring(resultString.indexOf("values_"+ddeName+"=")+8+ddeName.length(), resultString.indexOf(",;values_",resultString.indexOf("values_"+ddeName+"=")+8+ddeName.length()));			
				    valuesV=valuesSeq.split(",");
			    }
			    else if  (resultString.lastIndexOf("),")>0)//for dim>1
			    {
				    String valuesSeq=resultString.substring(resultString.indexOf("values_"+ddeName+"=(")+9+ddeName.length(), resultString.lastIndexOf("),"));			
				    valuesV=valuesSeq.split(",");
			    }
			    else if  (resultString.lastIndexOf(",")>0)//for dim=1
			    {
				    String valuesSeq=resultString.substring(resultString.indexOf("values_"+ddeName+"=")+8+ddeName.length(), resultString.lastIndexOf(","));			
				    valuesV=valuesSeq.split(",");
			    }*/
			}			
			for(int i=0;i<valuesV.length;i++)
			{
				values.add(valuesV[i]);
			}
			//System.out.println(timesSeq);
			input.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return values;		
	}
	public ArrayList<String> getErrors(){//get the error sequence from the simulation result file 'simResultAddr'
		ArrayList<String> errors= new ArrayList<String>();
		try {
			BufferedReader input=new BufferedReader(new FileReader(simResultAddr));
			String data="",resultString="";
			while((data=input.readLine())!=null)
			{
				resultString+=data;
			}
			String errorsSeq=resultString.substring(resultString.indexOf("errors=")+7, resultString.lastIndexOf(","));			
			String[] errorValues=errorsSeq.split(",");
			for(int i=0;i<errorValues.length;i++)
			{
				errors.add(errorValues[i]);
			}
			//System.out.println(timesSeq);
			input.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return errors;		
	}
	public boolean isLipschitzConstant()
	{
		// if odeString is Lipschitz Constant......
		// setL(lc); return true;
		// else  return false;
		return true;
	}
	public boolean isGAS()
	{
		// if odeString is GAS......
		// setEpoint(ep); setEtime(et); return true;
		// else  return false;
		return true;
	}
	public void comL()
	{
		//giving how to compute the LipschitzConstant
	}
	public void comEpoint()
	{
		//giving how to compute the Epoint
	}
	public void comEtime()
	{
		//giving how to compute the Etime
	}
	public String getDdeName() {
		return ddeName;
	}
	public void setDdeName(String ddeName) {
		this.ddeName = ddeName;
	}
	public String getSimResultAddr() {
		return simResultAddr;
	}
	public void setSimResultAddr(String simResultAddr) {
		this.simResultAddr = simResultAddr;
	}
	public String getDdeString() {
		return ddeString;
	}
	public void setDdeString(String ddeString) {
		this.ddeString = ddeString;
	}
	public float getL() {
		return L;
	}
	public void setL(float l) {
		L = l;
	}
	public float getEpoint() {
		return Epoint;
	}
	public void setEpoint(float epoint) {
		Epoint = epoint;
	}
	public float getEtime() {
		return Etime;
	}
	public void setEtime(float etime) {
		Etime = etime;
	}

}
