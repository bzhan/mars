package hcsp2sc;

public class ODE {//the ODE object 
	public String odeString;
	public float L;
	public float Epoint;
	public float Etime;
	
	public ODE (String ode)
	{
		odeString = ode;
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
	public String getOdeString() {
		return odeString;
	}
	public void setOdeString(String odeString) {
		odeString = odeString;
	}
	public float getL() {
		return L;
	}
	public void setL(float l) {
		this.L = l;
	}
	public float getEpoint() {
		return Epoint;
	}
	public void setEpoint(float epoint) {
		this.Epoint = epoint;
	}
	public float getEtime() {
		return Etime;
	}
	public void setEtime(float etime) {
		this.Etime = etime;
	}

}
