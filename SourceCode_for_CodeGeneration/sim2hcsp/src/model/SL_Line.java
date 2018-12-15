package model;

public class SL_Line {

	private SL_Block source;
	private SL_Block target;
	private int srcPort;
	private int dstPort;
	private int branch;
	private int partition;

	public SL_Line(SL_Block source, SL_Block target, int srcPort, int dstPort) {
		this.source = source;
		this.target = target;
		this.srcPort = srcPort;
		this.dstPort = dstPort;
		this.branch = 0;
		this.partition = -1;
	}

	public SL_Line(SL_Block source, SL_Block target, int srcPort, int dstPort, int branch) {
		this.source = source;
		this.target = target;
		this.srcPort = srcPort;
		this.dstPort = dstPort;
		this.branch = branch;
		this.partition = -1;
	}

	// interface for source
	public SL_Block getSource() {
		return source;
	}

	public void setSource(SL_Block b) {
		source = b;
	}

	public int getSrcPort() {
		return srcPort;
	}

	public void setSrcPort(int i) {
		srcPort = i;
	}

	public int getBranch() {
		return branch;
	}

	public void setBranch(int branch) {
		this.branch = branch;
	}

	public void setSource(SL_Block b, int i) {
		source = b;
		srcPort = i;
	}

	// interface for target
	public SL_Block getTarget() {
		return target;
	}

	public void setTarget(SL_Block b) {
		target = b;
	}

	public int getDstPort() {
		return dstPort;
	}

	public void setDstPort(int i) {
		dstPort = i;
	}

	public void setTarget(SL_Block b, int i) {
		target = b;
		dstPort = i;
	}

	// for communication names
	public void setPartition(int i) {
		this.partition = i;
	}

	public String getChName() {
		return source.getName() + "_" + srcPort + "_" + partition;
	}

	public String getVarName() {
		return source.getName() + "_" + srcPort;
	}

	// for print
	public void printLine(int level) {
		String head = Utilize.tabsAhead(level);
		System.out.println(head + "\t" + "(" + source.getName() + "," + srcPort + "," + branch + ")"
				+ " --> (" + target.getName() + "," + dstPort + ")" + this.partition);
	}

}
