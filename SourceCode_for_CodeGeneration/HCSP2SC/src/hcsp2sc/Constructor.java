package hcsp2sc;

public class Constructor {// different kinds of constructors
	public enum constructorType{PROC,SKIP,ASSI,WAIT,CHRE,CHSE,COND,UNDE,STAR,ODE,ODE_INT,DDE,DDE_INT};
	public constructorType Type;
	public String Content;
	public Constructor(constructorType type,String content) {
		Type = type;
		Content = content;
	}
	public constructorType getType() {
		return Type;
	}
	public void setType(constructorType type) {
		this.Type = type;
	}
	public String getContent() {
		return Content;
	}
	public void setContent(String content) {
		this.Content = content;
	}	
	public String duration(){
		switch (Type){
			case WAIT: return Content.substring(Content.indexOf("(")+1,Content.indexOf(")")).replaceAll(" ","");
			default:   return "";
		}
	}

}
