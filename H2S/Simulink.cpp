#include "Simulink.h"
#include <fstream>

vector<Block> Simulink::blocklist;  //Actually define the static member
vector<Line> Simulink::linelist;
vector<Subsystem> Simulink::sublist;

int Simulink::subSysName = 0;
int Simulink::inName = 0;
int Simulink::outName = 0;
int Simulink::conName = 0;
int Simulink::sumName = 0;
int Simulink::productName = 0;
int Simulink::logicalOptName = 0;
int Simulink::relationalOptName = 0;
int Simulink::intName = 0;
int Simulink::indexName = 0;
int Simulink::delayName = 0;
int Simulink::randomName = 0;
int Simulink::switchName = 0;
int Simulink::scopeName = 0;

void Simulink::addBlock(int sid,string bt,string bn,string bv,int bp,string bo,string bi,int x1,int y1,int x2,int y2)
{
  Block blk(sid,bt,bn,bv,bp,bo,bi,x1,y1,x2,y2);
  blocklist.push_back(blk);
  return;
}

void Simulink::insertHeadBlock(int sid,string bt,string bn,string bv,int bp,string bo,string bi,int x1,int y1,int x2,int y2)
{
  Block blk(sid,bt,bn,bv,bp,bo,bi,x1,y1,x2,y2);
  blocklist.insert(blocklist.begin(),blk);
  return;
}

void Simulink::printBlocklist()
{
  vector<Block>::iterator it;

  for(it=blocklist.begin();it!=blocklist.end();it++)
  {
    cout<<(*it).sID<<"\t"<<(*it).blockType<<"\t"<<(*it).blockName<<endl;
  }
  return;
}

bool Simulink::inBlocklist(string bn)
{
  vector<Block>::iterator it;
  for(it=blocklist.begin();it!=blocklist.end();it++)
  {
    if((*it).blockName == bn)
      return true;
  }
  return false;
}

// bool Simulink::inThisBlocklist(int s,string bn) //ignore blocks between an "EndSubSystem" and a "SubSystem"
// {
//   string head = "\"SubSystem"+to_string(s)+"\"";
//   string tail = "\"EndSubSystem"+to_string(s)+"\"";
//   vector<Block>::iterator it,it1,it2;

//   // if(bn == head || bn ==tail)
//   //   return true;
//   for(it=blocklist.begin();it!=blocklist.end()-1;it++)
//   {
//     if((*it).blockName == head)
//     {
//       for(it1=it+1;it1!=blocklist.end();it1++)
//       {
//       	if((*it1).blockType=="SubSystem" || (*it1).blockType=="EndSubSystem")
//       	  break;
//       	if((*it1).blockName == bn)
//       	  return true;
//       }
//       break;
//     }
//   }
//   for(it=blocklist.end()-1;it!=blocklist.begin()+1;it--) //Reverse search from end()-1, not from end().
//   {
//     if((*it).blockName == tail)
//     {
//       for(it2=it-1;it2!=blocklist.begin();it2--)
//       {
//       	if((*it2).blockType=="SubSystem" || (*it2).blockType=="EndSubSystem")
//       	  break;
//       	if((*it2).blockName == bn)
//       	  return true;
//       }
//       break;
//     }
//   }
//   return false;
// }

bool Simulink::inThisBlocklist(int s,string bn)
{
  vector<Block>::iterator it;
  
  for(it=blocklist.begin();it!=blocklist.end();it++)
    if((*it).sID == s && (*it).blockName == bn)
      return true;
  return false;
}

int Simulink::inWhichBlocklist(string bn)
{
  for(int s=1;s<=subSysName;s++)
    if(inThisBlocklist(s,bn))
      return s;
  return -1;
}

void Simulink::addLine(int sid,string sb,int sp,string db,int dp)
{
  Line lne(sid,sb,sp,db,dp);
  linelist.push_back(lne);
  return;
}

void Simulink::insertHeadLine(int sid,string sb,int sp,string db,int dp)
{
  Line lne(sid,sb,sp,db,dp);
  linelist.insert(linelist.begin(),lne);
  return;
}

void Simulink::cutLine(int sid,string sb,int sp,string db,int dp)
{
  vector<Line>::iterator it;
  for(it=linelist.begin();it!=linelist.end();it++)
  {
    if(it->sID == sid && it->srcBlock == sb && it->srcPort == sp && it->dstBlock == db && it->dstPort == dp)
    {
      it = linelist.erase(it);
      it--;
      break;
    }
  }
  return;
}

void Simulink::breakLine(int sid,string bb,int bi,int bo,string db,int dp)
{
  vector<Line>::iterator it;
  for(it=linelist.begin();it!=linelist.end();it++)
  {
    if(it->sID == sid && it->dstBlock == db && it->dstPort == dp)
    {
      Line lne(sid,it->srcBlock,it->srcPort,bb,bi);
      Line lne1(sid,bb,bo,db,dp);

      it = linelist.erase(it);
      it--;

      it = linelist.insert(it,lne);
      linelist.insert(it,lne1);
      break;
    }
  }
  return;
}

void Simulink::printLinelist()
{
  vector<Line>::iterator it1;

  cout<<endl;
  for(it1=linelist.begin();it1!=linelist.end();it1++)
    cout<<(*it1).sID<<"\t"<<(*it1).srcBlock<<","<<(*it1).srcPort<<"\t"<<"->"<<"\t"<<(*it1).dstBlock<<","<<(*it1).dstPort<<endl;
  cout<<endl;
}

bool Simulink::inThisLinelist(int sid,string sb,int sp)
{
  vector<Line>::iterator it;
  for(it=linelist.begin();it!=linelist.end();it++)
  {
    if(it->sID == sid && it->srcBlock == sb && it->srcPort == sp)
    {
      return true;
    }
  }
  return false;
}

void Simulink::addSubsystemInport(string sname,int index,string inname)
{
  vector<Subsystem>::iterator its;

  for(its=sublist.begin();its!=sublist.end();its++)
  {
    if(its->name == sname)
    {
      its->inList.insert(pair<int,string>(index,inname));
      return;
    }
  }
  Subsystem subs(sname,index,inname,-1,"");
  sublist.push_back(subs);

  return;
}

void Simulink::addSubsystemOutport(string sname,int index,string outname)
{
  vector<Subsystem>::iterator its;

  for(its=sublist.begin();its!=sublist.end();its++)
  {
    if(its->name == sname)
    {
      its->outList.insert(pair<int,string>(index,outname));
      return;
    }
  }
  Subsystem subs(sname,-1,"",index,outname);
  sublist.push_back(subs);

  return;
}

void Simulink::getSubsystemInport(string signal,string& sname,int& index)
{
  vector<Subsystem>::iterator its;
  map<int,string>::iterator itp;
  signal = "\"In_"+signal+"\"";

  for(its=sublist.begin();its!=sublist.end();its++)
  {
    for(itp=its->inList.begin();itp!=its->inList.end();itp++)
    {
      if(itp->second == signal)
      {
	sname = its->name;
	index = itp->first;
	return;
      }
    }
  }
  sname = "";
  index = -1;
  
  return;
}

string Simulink::getSubsystemInport(string sname,int index)
{
  vector<Subsystem>::iterator its;
  map<int,string>::iterator itp;

  for(its=sublist.begin();its!=sublist.end();its++)
  {
    if(its->name == sname)
    {
      for(itp=its->inList.begin();itp!=its->inList.end();itp++)
      {
	if(itp->first == index)
	  return itp->second;
      }
    }
  }
  return "";
}

string Simulink::getSubsystemOutport(string sname,int index)
{
  vector<Subsystem>::iterator its;
  map<int,string>::iterator itp;

  for(its=sublist.begin();its!=sublist.end();its++)
  {
    if(its->name == sname)
    {
      for(itp=its->outList.begin();itp!=its->outList.end();itp++)
      {
	if(itp->first == index)
	  return itp->second;
      }
    }
  }
  return "";
}

void Simulink::getSubsystemOutport(string signal,string& sname,int& index)
{
  vector<Subsystem>::iterator its;
  map<int,string>::iterator itp;
  signal = "\"Out_"+signal+"\"";

  for(its=sublist.begin();its!=sublist.end();its++)
  {
    for(itp=its->outList.begin();itp!=its->outList.end();itp++)
    {
      if(itp->second == signal)
      {
	sname = its->name;
	index = itp->first;
	return;
      }
    }
  }
  sname = "";
  index = -1;
  
  return;
}

void Simulink::toMdl()
{
  ifstream in("h2sbak.mdl",ios::in);
  ofstream out("h2s.mdl",ios::out);
  if(!in.is_open())
  {
    cout<<"Error opening file h2sbak.mdl"<<endl;
    exit(1);
  }
  out<<in.rdbuf();   //Rewrite h2s.mdl from h2sbak.mdl
  out.close();
  in.close();
  
  ofstream h2s("h2s.mdl",ios::app);
  if(!h2s.is_open())
  {
    cout<<"Error opening file h2s.mdl"<<endl;
    exit(1);
  }
  
  vector<Block>::iterator it = blocklist.begin();
  vector<Line>:: iterator it1 = linelist.begin();
  vector<Line>:: iterator it2; //For line branching

  printBlocklist();
  printLinelist();

  while(it != blocklist.end() || it1 != linelist.end())
    {
      while(it != blocklist.end())
	{
	  if((*it).blockType == "EndSubSystem")
	    {
	      it++;
	      continue;
	    }
	  if((*it).blockType == "SubSystem")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Ports		      ["<<(*it).blockPorts<<",1]\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      MinAlgLoopOccurrences   off\n";
	      h2s<<"      PropExecContextOutsideSubsystem off\n";
	      h2s<<"      RTWSystemCode	      \"Auto\"\n";
	      h2s<<"      FunctionWithSeparateData off\n";
	      h2s<<"      Opaque		      off\n";
	      h2s<<"      RequestExecContextInheritance off\n";
	      h2s<<"      MaskHideContents	      off\n";
	      h2s<<"      System {\n";
	      h2s<<"        Name			"<<(*it).blockName<<"\n";
	      h2s<<"        Open			off\n";
	      h2s<<"        ModelBrowserVisibility	off\n";
	      h2s<<"        ModelBrowserWidth	200\n";
	      h2s<<"        ScreenColor		\"white\"\n";
	      h2s<<"        PaperOrientation	\"landscape\"\n";
	      h2s<<"        PaperPositionMode	\"auto\"\n";
	      h2s<<"        PaperType		\"usletter\"\n";
	      h2s<<"        PaperUnits		\"inches\"\n";
	      h2s<<"        TiledPaperMargins	[0.500000, 0.500000, 0.500000, 0.500000]\n";
	      h2s<<"        TiledPageScale		1\n";
	      h2s<<"        ShowPageBoundaries	off\n";
	      h2s<<"        ZoomFactor		\"100\"\n";
	    }
	  else if((*it).blockType == "Outport")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      IconDisplay             \"Port number\"\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "Inport")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      IconDisplay             \"Port number\"\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "EnablePort")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Ports		      []\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "UnitDelay")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      BlockMirror	      on\n";
	      h2s<<"      X0		      "<<(*it).blockValue<<"\n";
	      h2s<<"      InputProcessing	      \"Elements as channels (sample based)\""<<"\n";
	      h2s<<"      SampleTime	      \"0\""<<"\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "RandomNumber")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      SampleTime	      \"15\""<<"\n"; //need to be long enough, otherwise Internal Choice will vibrate
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "RateTransition")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      // h2s<<"      SampleTime	      "<<(*it).blockValue<<"\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "Switch")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      Criteria		      \"u2 > Threshold\""<<"\n";
	      h2s<<"      InputSameDT	      off"<<"\n";
	      h2s<<"      SaturateOnIntegerOverflow	off"<<"\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "DataTypeConversion")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      OutDataTypeStr	      "<<(*it).blockOperator<<"\n";
	      h2s<<"      RndMeth		      \"Floor\""<<"\n";
	      h2s<<"      SaturateOnIntegerOverflow	off"<<"\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "Scope")
	  {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Ports		      ["<<(*it).blockPorts<<"]\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"      Floating		      off\n";
	      // h2s<<"      AutoScale		      on\n";
	      h2s<<"      Open		      off\n";
	      h2s<<"      NumInputPorts	      \""<<(*it).blockPorts<<"\"\n";
	      // h2s<<"      List {\n";
	      // h2s<<"	ListType		AxesTitles\n";
	      // h2s<<"	axes1			\"%<SignalLabel>\"\n";
	      // h2s<<"	axes2			\"%<SignalLabel>\"\n";
	      // h2s<<"      }\n";
	      h2s<<"      List {\n";
	      h2s<<"	ListType		ScopeGraphics\n";
	      h2s<<"	FigureColor		\"[0.5 0.5 0.5]\"\n";
	      h2s<<"	AxesColor		\"[0 0 0]\"\n";
	      h2s<<"	AxesTickColor		\"[1 1 1]\"\n";
	      h2s<<"	LineColors		\"[0 1 0;1 0 1;0 1 1;1 0 0;0 1 0;0 0 1]\"\n";
	      h2s<<"	LineStyles		\"-|-|-|-|-|-\"\n";
	      h2s<<"	LineWidths		\"[1 1 1 1 1 1]\"\n";
	      h2s<<"	MarkerStyles		\"none|none|none|none|none|none\"\n";
	      h2s<<"      }\n";
	      h2s<<"      ShowLegends	      off\n";
	      // h2s<<"      YMin		      \"-5~-5\"\n";
	      // h2s<<"      YMax		      \"5~5\"\n";
	      h2s<<"      DataFormat	      \"StructureWithTime\"\n";
	      h2s<<"      SampleTime	      \"0\"\n";
	      h2s<<"    }\n";
	  }
	  else if((*it).blockType == "Constant")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Value		      "<<(*it).blockValue<<"\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "Sum" || (*it).blockType == "Product")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Ports		      ["<<(*it).blockPorts<<",1]\n";
	      h2s<<"      Inputs		      \""<<(*it).blockInputs<<"\"\n";
	      h2s<<"      InputSameDT	      off\n";
	      h2s<<"      OutDataTypeStr	      \"Inherit: Inherit via internal rule\"\n";
	      h2s<<"      SaturateOnIntegerOverflow	off\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "Logic" || (*it).blockType == "RelationalOperator")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Ports		      ["<<(*it).blockPorts<<",1]\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      if((*it).blockInputs != "")
		h2s<<"      Inputs		      \""<<(*it).blockInputs<<"\"\n";
	      h2s<<"      Operator		      "<<(*it).blockOperator<<"\n";
	      h2s<<"      OutDataTypeStr	      \"boolean\"\n";
	      h2s<<"    }\n";
	    }
	  else if((*it).blockType == "Integrator")
	    {
	      h2s<<"    Block {\n";
	      h2s<<"      BlockType		      "<<(*it).blockType<<"\n";
	      h2s<<"      Name		      "<<(*it).blockName<<"\n";
	      h2s<<"      Ports		      ["<<(*it).blockPorts<<",1]\n";
	      h2s<<"      Position		      ["<<(*it).bx1<<", "<<(*it).by1<<", "<<(*it).bx2<<", "<<(*it).by2<<"]\n";
	      h2s<<"    }\n";
	    }
	  it++;

	  if(it != blocklist.end() && (*it).blockType == "EndSubSystem")
	    break;
	}

      while(it1 != linelist.end())
	{
	  int branch;
	  int firstBranch;
	  branch = 0;
	  firstBranch = 1;

	  if((*it1).dstBlock == "-----------" || (*it1).dstBlock == "~~~~~~~~~~~")
	    {
	      it1++;
	      continue;
	    }

	  h2s<<"    Line {\n";
	  h2s<<"      SrcBlock		      "<<(*it1).srcBlock<<"\n";
	  h2s<<"      SrcPort		      "<<(*it1).srcPort<<"\n";
	  for(it2=it1+1;it2!=linelist.end();it2++)
	    {
	      if((*it1).dstBlock != "~~~~~~~~~~~" && (*it2).srcBlock == (*it1).srcBlock && (*it2).srcPort == (*it1).srcPort && (*it2).sID == (*it1).sID)
		{
		  branch = 1;
		  if(firstBranch)
		    {
		      firstBranch = 0;
		      h2s<<"      Points		      [20,0]\n";
		      h2s<<"	Branch {\n";
		      h2s<<"	  DstBlock		    "<<(*it1).dstBlock<<"\n";
		      if((*it1).dstPort == 'e')
		  	h2s<<"	  DstPort		    enable\n";
		      else
		  	h2s<<"	  DstPort		    "<<(*it1).dstPort<<"\n";
		      h2s<<"      }\n";
		    }
		  h2s<<"	Branch {\n";
		  h2s<<"	  DstBlock		    "<<(*it2).dstBlock<<"\n";
		  if((*it2).dstPort == 'e')
		    h2s<<"	  DstPort		    enable\n";
		  else
		    h2s<<"	  DstPort		    "<<(*it2).dstPort<<"\n";
		  h2s<<"      }\n";
		  it2 = linelist.erase(it2);   //relocated dangling pointer
		  it2--; //kick it2 back to avoid missing element.
		  if(it2 == linelist.end())
		    break;
		}
	    }
	  if(!branch)
	    {
	      h2s<<"      DstBlock		      "<<(*it1).dstBlock<<"\n";
	      if((*it1).dstPort == 'e')
		h2s<<"      DstPort		      enable\n";
	      else
		h2s<<"      DstPort		      "<<(*it1).dstPort<<"\n";
	    }
	  h2s<<"    }\n";

	  it1++;

	  if(it1 !=linelist.end() && (*it1).dstBlock == "~~~~~~~~~~~")
	    break;
	}
      h2s<<"    }\n  }\n";
    }

  h2s<<"  }\n  }\n";    //Put two '}' at the end of file

  h2s.close();

  return;
}
