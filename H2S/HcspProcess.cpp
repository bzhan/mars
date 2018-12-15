#include "HcspProcess.h"

int HcspProcess:: getOpType(string name)
{
  if(name[0] == '+' || name[0] == '-')
    return 1;
  else if(name[0] == '*' || name[0] == '/')
    return 2;
  else if(name[0] == '&' || name[0] == '|' || name == "~" || name == "=" || name == "<" || name == ">")
    return 3;
  else if(name == "DIFF" || name == "\'=")
    return 4;
  else if(name == "AND")
    return 11;
  else if(name == ":=")
    return 12;
  else if(name == "IMP")
    return 13;
  else if(name == "LI")
    return 14;
  else if(name == ";")
    return 15;
  else if(name == "REP")
    return 16;
  else if(name == "?")
    return 17;
  else if(name == "!")
    return 18;
  else if(name == "[[>")
    return 19;
  else if(name == "[[")
    return 20;
  else if(name == "CON")
    return 21;
  else
    return -1;
}

void HcspProcess:: toSimulink(Node* p)
{
  // Node* root = p;
  int k;
  blockPosition blkpos;

  //Simulink::inName = 0;
  //Simulink::outName = 0;

  // Simulink::subSysName++;
  // Simulink::insertHeadBlock(Simulink::subSysName,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",25,28,195,112);
  // // Simulink::addBlock(Simulink::subSysName,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",25+(Simulink::subSysName-1)*200,28,195+(Simulink::subSysName-1)*200,112);
  // Simulink::insertHeadLine(Simulink::subSysName,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);

  toSimulink1(p);
  // toSimulink1(p,root);

  for(k=1;getBlockInfoInport(p,k)!="";k++) //Inputs at level 0 (including ok)
  {
    string s = getBlockInfoInport(p,k);
    if(s == "\"In_ok\"")
    {
      Simulink::conName++;
      // blkpos = getBlkPos();
      Simulink::addBlock(0,"Constant","\"Constant"+to_string(Simulink::conName)+"\"","1",0,"","",190, 170, 220, 190);
      // blkpos = getBlkPos();
      Simulink::addBlock(0,"DataTypeConversion","\"Data Type Conversion\"","",0,"\"boolean\"","",285, 280, 345, 300);
      Simulink::addLine(0,"\"Constant"+to_string(Simulink::conName)+"\"",1,"\"Data Type Conversion\"",1);
      Simulink::addLine(0,"\"Data Type Conversion\"",1,getBlockInfoName(p),k);
      continue;
    }
    // Simulink::randomName++; //No need to give random number
    // blkpos = getBlkPos();
    // Simulink::addBlock(0,"RandomNumber","\"Random\\nNumber"+to_string(Simulink::randomName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
    // Simulink::addLine(0,"\"Random\\nNumber"+to_string(Simulink::randomName)+"\"",1,getBlockInfoName(p),k);
  }

  for(k=1;getBlockInfoOutport(p,k)!="";k++) //Plug a multiple-axi-Scope here for outputs (including ok')
  {}
  Simulink::scopeName++;
  // blkpos = getBlkPos();
  Simulink::addBlock(0,"Scope","\"Scope"+to_string(Simulink::scopeName)+"\"","",k-1,"","",735, 259, 800, 381);
  for(k=1;getBlockInfoOutport(p,k)!="";k++)
  {
    Simulink::addLine(0,getBlockInfoName(p),k,"\"Scope"+to_string(Simulink::scopeName)+"\"",k);
  }
  
  // Simulink::addBlock(Simulink::subSysName,"EndSubSystem","\"EndSubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",0,0,0,0);
  // Simulink::addLine(Simulink::subSysName,"~~~~~~~~~~"+to_string(Simulink::subSysName),-1,"~~~~~~~~~~~",-1);

  return;
}

void HcspProcess:: toSimulink1(Node* p)
{
  int i,k;
  string DstBlock = "";
  string SrcBlock = "";
  blockPosition blkpos;
  int tempSID = -1;
  // string tempDstBlock = "";
  // int tempDstPort = -1;
  // int tempDstPort1 = -1;

  tempSID = Simulink::subSysName;

  switch(p->type)
  {
    case TYPE_CONTENT:
    {
      if(p->content == "skip")
      {
	DstBlock = "";

	blkpos = getBlkPos();
	Simulink::subSysName++;
	Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	tempSID = Simulink::subSysName;

	Simulink::inName = 0;
	Simulink::outName = 0;

	Simulink::inName++; //Add ok
	// blkpos = getBlkPos();
	Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",195, 263, 225, 277);
	addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");

	Simulink::outName++; //Add ok'
	// blkpos = getBlkPos();
	Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",430, 263, 460, 277);
	addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	Simulink::addLine(tempSID,"\"In_ok\"",1,"\"Out_ok\"",1);

	Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	return;
      }
      else
      {
	blkpos = getBlkPos();
	Simulink::addBlock(tempSID,"Constant","\"Constant"+to_string(Simulink::conName)+"\"",p->content,0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
      }
    }break;
    case TYPE_INDEX:
    {

    }break;
    case TYPE_OP:
    {
      switch(getOpType(p->op.name))
      {
        case 1:       //'+' '-'
	{
	  DstBlock = "\"Add"+to_string(Simulink::sumName)+"\"";
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Sum",DstBlock,"",p->op.num,"",p->op.name,blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	} break;
        case 2:       //'*' '/'
	{
	  DstBlock = "\"Divide"+to_string(Simulink::productName)+"\"";
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Product",DstBlock,"",p->op.num,"",p->op.name,blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	} break;
        case 3:       //Bool expressions
	{
	  return;
	}break;
        case 4:       //Differential equations
	{
	  return;
	}break;
        case 11:      //Continuous Evolution "AND"("&&")
	{
	  // cout<<getBlockInfoName(p->op.node[0])<<"\t"<<getBlockInfoOutport(p->op.node[0],"\"Out_t\"")<<"\t"<<getBlockInfoInport(p->op.node[0],"\"In_a\"")<<endl;
	  // cout<<getBlockInfoName(p->op.node[1])<<"\t"<<getBlockInfoOutport(p->op.node[1],"\"Out1\"")<<"\t"<<getBlockInfoInport(p->op.node[1],"\"In_t\"")<<endl;
	  // Simulink::subSysName++;
	  // Simulink::insertBeforeBlock(getBlockInfoName(p->op.node[0]),"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",25+(Simulink::subSysName-1)*200,28,195+(Simulink::subSysName-1)*200,112); //Insert a head-block and a head-line before head of current subsystem.

	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  DifferentialEquations dequ(p->op.node[0]);
	  //dequ.autoLayout(dequ.getRoot());
	  dequ.toSimulink(dequ.getRoot(),tempSID);
	  BoolExpression bexp(p->op.node[1]);
	  //bexp.autoLayout(bexp.getRoot());
	  bexp.toSimulink(bexp.getRoot(),tempSID);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  Simulink::inName++; //Add ok
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",75, 150, 105, 170);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");
	  Simulink::outName++; //Add ok'
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",1235, 70, 1265, 90);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  // blkpos = getBlkPos();
	  // Simulink::logicalOptName++;
	  // string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  // Simulink::addBlock(tempSID,"Logic",blockAnd1,"",2,"\"AND\"",to_string(p->op.num),blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd2,"",2,"\"AND\"",to_string(p->op.num),465, 225, 495, 245);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd3 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd3,"",2,"\"AND\"",to_string(p->op.num),655, 70, 685, 90);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockNot,"",1,"\"NOT\"","",380, 30, 410, 50);

	  // // blkpos = getBlkPos();
	  // Simulink::delayName++; //delay here is not needed anymore, fixed on Feb 7, 2015
	  // string blockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  // Simulink::addBlock(tempSID,"UnitDelay",blockDelay1,"\"1\"",0,"","",380, 95, 410, 115);
	  // // blkpos = getBlkPos();
	  // // Simulink::delayName++;
	  // // string blockDelay2 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  // // Simulink::addBlock(tempSID,"UnitDelay",blockDelay2,"\"1\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),1,blockDelay1,1); //Break the algebraic loop  //delay here is not needed anymore, fixed on Feb 7, 2015
	  // Simulink::addLine(tempSID,blockDelay1,1,blockAnd1,1);
	  // Simulink::addLine(tempSID,blockDelay1,1,blockAnd2,2);
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),1,blockAnd2,2);


	  // Simulink::addLine(tempSID,blockAnd1,1,blockDelay2,1);
	  // Simulink::addLine(tempSID,blockDelay2,1,blockAnd1,2);

	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd2,1);
	  // Simulink::addLine(tempSID,blockAnd1,1,blockAnd2,2);
	  // Simulink::addLine(tempSID,blockAnd1,1,getBlockInfoName(p->op.node[0]),'e');
	  // Simulink::addLine(tempSID,blockAnd2,1,blockAnd1,1);
	  // Simulink::addLine(tempSID,blockAnd2,1,getBlockInfoName(p->op.node[0]),'e'); //use an inport other than enableport, fixed on Feb 7, 2015
	  Simulink::addLine(tempSID,blockAnd2,1,getBlockInfoName(p->op.node[0]),getBlockInfoInport(p->op.node[0],"\"In_enable\""));

	  // Simulink::addLine(tempSID,blockDelay1,1,blockNot,1); //delay here is not needed anymore, fixed on Feb 7, 2015
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),1,blockNot,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd3,1);
	  Simulink::addLine(tempSID,blockNot,1,blockAnd3,2);
	  Simulink::addLine(tempSID,blockAnd3,1,"\"Out_ok\"",1);

	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Draw lines from F to B in terms of <F&&B>
	  {
	    int count = 0;
	    string s= getBlockInfoInport(p->op.node[1],k);
	    s = s.replace(1,2,"Out");
	    int m = getBlockInfoOutport(p->op.node[0],s);
	    if(m != -1)
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,getBlockInfoName(p->op.node[1]),k);
	    else
	    {
	      s = s.replace(1,3,"In");
	      m = getBlockInfoInport(p->op.node[0],s);
	      if(m != -1)
		Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);
	      else
	      {
		Simulink::inName++;
		count++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",s,"",0,"","",655, 475+65*count, 685, 495+65*count);
		addBlockInfoInport(p,Simulink::inName,s);
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
		Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);

		string s1 = s;  //output signal used in B while not in P, added on Feb 7, 2015
		s = s.replace(1,2,"Out");
		Simulink::outName++;
		Simulink::addBlock(tempSID,"Outport",s,"",0,"","",755, 485+65*count, 785, 505+65*count);
		addBlockInfoOutport(p,Simulink::outName,s);
		Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
		Simulink::addLine(tempSID,s1,1,s,1);
	      }
	    }
	  }

	  // for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Plug a multiple-axi-Scope here
	  // {}
	  // Simulink::scopeName++;
	  // blkpos = getBlkPos();
	  // Simulink::addBlock(tempSID,"Scope","\"Scope"+to_string(Simulink::scopeName)+"\"","",k-1,"","",blkpos.x1,blkpos.y1,blkpos.x2+10,blkpos.y2+30);
	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Add outports
	  {
	    Simulink::outName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",getBlockInfoOutport(p->op.node[0],k),"",0,"","",1235, 140+65*k, 1265, 160+65*k);
	    addBlockInfoOutport(p,Simulink::outName,getBlockInfoOutport(p->op.node[0],k));
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,getBlockInfoOutport(p->op.node[0],k));
	    Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,getBlockInfoOutport(p->op.node[0],k),1);

	    // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,"\"Scope"+to_string(Simulink::scopeName)+"\"",k);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Add inports
	  {
	    if(getBlockInfoInport(p->op.node[0],k) == "\"In_enable\"")
	      continue;
	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[0],k),"",0,"","",75, 330+65*k, 105, 350+65*k);
	    addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[0],k));
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[0],k));
	    Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[0],k),1,getBlockInfoName(p->op.node[0]),k);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Switch inport&outport signal according to ok & d(B)
	  {
	    if(getBlockInfoInport(p->op.node[0],k) == "\"In_enable\"")
	      continue;
	    string si = getBlockInfoInport(p->op.node[0],k);
	    string so = si.replace(1,2,"Out");
	    si = getBlockInfoInport(p->op.node[0],k);

	    Simulink::switchName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",1085, 135+65*k, 1135, 165+65*k);

	    Simulink::breakLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,1,so,1);
	    Simulink::addLine(tempSID,si,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	    Simulink::addLine(tempSID,"\"In_ok\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	    // Simulink::addLine(tempSID,blockAnd2,1,"\"Switch"+to_string(Simulink::switchName)+"\"",2); //use en other than ok to switch outputs, fixed on Feb 7, 2015
	  }

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	}break;
        case 12:      //Assignment ":="
	{
	  int k;
	  //Simulink::getSubsystemInport(p->op.node[0]->index,DstBlock,tempDstPort);
	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  Simulink::inName++; //Add ok
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",110, 75, 140, 95);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");
	  Simulink::outName++; //Add ok'
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",1015, 75, 1045, 95);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  // blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay,"\"0\"",0,"","",395, 100, 425, 120);

	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockDelay,1);
	  // Simulink::addLine(tempSID,blockDelay,1,"\"Out_ok\"",1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,"\"Out_ok\"",1);

	  DstBlock = "\"Out_"+p->op.node[0]->index+"\"";

	  if(!Simulink::inThisBlocklist(tempSID,DstBlock))
	  {
	    Simulink::outName++;  //Add an outport for the assigned signal
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",DstBlock,"",0,"","",1015, 315, 1045, 335);
	    addBlockInfoOutport(p,Simulink::outName,DstBlock);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,DstBlock);
	  }

	  if((p->op.node[1])->type == TYPE_CONTENT)
          {
	    Simulink::conName++;
	    SrcBlock = "\"Constant"+to_string(Simulink::conName)+"\"";
	  }
	  else if(p->op.node[1]->type == TYPE_INDEX)
	  {
	    SrcBlock = "\"In_"+p->op.node[1]->index+"\"";
	    if(!Simulink::inThisBlocklist(tempSID,SrcBlock))
	    {
	      Simulink::inName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Inport",SrcBlock,"0",0,"","",110, 320, 140, 340);
	      addBlockInfoInport(p->op.node[1],Simulink::inName,SrcBlock);
	      Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,SrcBlock);
	    }
	    string tempBlock = SrcBlock.replace(1,2,"Out");
	    SrcBlock = SrcBlock.replace(1,3,"In");
	    if(!Simulink::inThisBlocklist(tempSID,tempBlock))
	    {
	      Simulink::outName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",tempBlock,"0",0,"","",1015, 445, 1045, 465);
	      addBlockInfoOutport(p->op.node[1],Simulink::outName,tempBlock);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,tempBlock);
	    }
	    Simulink::addLine(tempSID,SrcBlock,1,tempBlock,1); //Directly output the unchanged inport
	  }
	  else if((p->op.node[1])->type == TYPE_OP)
	  {
	    switch(getOpType((p->op.node[1])->op.name))
	    {
	      case 1:
	      {
		Simulink::sumName++;
		SrcBlock = "\"Add"+to_string(Simulink::sumName)+"\"";
	      } break;
	      case 2:
	      {
		Simulink::productName++;
		SrcBlock = "\"Divide"+to_string(Simulink::productName)+"\"";
	      } break;
	      default: break;
	    }
	  }
	  if(SrcBlock != "" && DstBlock != "")
	  {
	    Simulink::addLine(tempSID,SrcBlock,1,DstBlock,1);
	  }

	  toSimulink1(p->op.node[1]);

	  for(k=1;Simulink::getSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",k)!="";k++)//Add all the inports in the current Assignment subsystem to the current node ":="
	  {
	    string s = Simulink::getSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",k);
	    addBlockInfoInport(p,k,s);
	  }
	  for(k=1;Simulink::getSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",k)!="";k++)//Add all the outports in the current Assignment subsystem to the current node ":="
	  {
	    string s = Simulink::getSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",k);
	    addBlockInfoOutport(p,k,s);
	  }

	  Simulink::cutLine(tempSID,"\"In_"+p->op.node[0]->index+"\"",1,DstBlock,1); //Cut the redundant line

	  if(!Simulink::inThisBlocklist(tempSID,"\"In_"+p->op.node[0]->index+"\"")) 
	  {
	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport","\"In_"+p->op.node[0]->index+"\"","",0,"","",110, 190, 140, 210);
	    addBlockInfoInport(p,Simulink::inName,"\"In_"+p->op.node[0]->index+"\"");
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_"+p->op.node[0]->index+"\"");
	  }

	  Simulink::switchName++; //Switch the changed signal according to ok and ok'
	  // blkpos = getBlkPos();
	  string blockSwitch1 = "\"Switch"+to_string(Simulink::switchName)+"\"";
	  Simulink::addBlock(tempSID,"Switch",blockSwitch1,"",0,"","",585, 225, 635, 255);
	  Simulink::switchName++;
	  // blkpos = getBlkPos();
	  string blockSwitch2 = "\"Switch"+to_string(Simulink::switchName)+"\"";
	  Simulink::addBlock(tempSID,"Switch",blockSwitch2,"",0,"","",740, 360, 790, 390);
	  // blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay1,"\"0\"",0,"","",750, 295, 780, 315);

	  Simulink::breakLine(tempSID,blockSwitch1,1,1,DstBlock,1);
	  Simulink::addLine(tempSID,"\"In_"+p->op.node[0]->index+"\"",1,blockSwitch1,3);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockSwitch1,2);

	  Simulink::breakLine(tempSID,blockSwitch2,3,1,DstBlock,1);
	  Simulink::addLine(tempSID,blockSwitch2,1,blockDelay1,1);
	  Simulink::addLine(tempSID,blockDelay1,1,blockSwitch2,1);
	  Simulink::addLine(tempSID,blockDelay,1,blockSwitch2,2);


	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 13:      //Conditional "IMP"("->")
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;
	  
	  BoolExpression bexp(p->op.node[0]);
	  bexp.toSimulink(bexp.getRoot(),tempSID);
	  toSimulink1(p->op.node[1]);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Inports of P (including ok)
	  {
	    int count = 0;
	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[1],k),"",0,"","",155, 135+65*(k-1), 185, 155+65*(k-1));
	    addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[1],k));
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[1],k));
	    if(getBlockInfoInport(p->op.node[1],k) == "\"In_ok\"") //ok_P = ok&B
	    {
	      Simulink::logicalOptName++;
	      Simulink::addBlock(tempSID,"Logic","\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"","",2,"\"AND\"","2",225, 160+65*(k-1), 255, 180+65*(k-1));
	      Simulink::addLine(tempSID,"\"In_ok\"",1,"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",1);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),1,"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",2);
	      Simulink::addLine(tempSID,"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",1,getBlockInfoName(p->op.node[1]),k);
	    }
	    else
	      Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[1],k),1,getBlockInfoName(p->op.node[1]),k);

	    string s = getBlockInfoInport(p->op.node[1],k);
	    s = s.replace(1,2,"Out");
	    int m = getBlockInfoOutport(p->op.node[1],s);
	    if(m == -1)
	    {
	      Simulink::outName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1010, 485+65*count, 1040, 505+65*count);
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,s.replace(1,3,"In"),1,s,1);
	      s = s.replace(1,2,"Out");
	      count++;
	    }
	  }

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Inports of B
	  {
	    int count = 0;
	    string s = getBlockInfoInport(p->op.node[0],k);
	    int m = getBlockInfoInport(p->op.node[1],s);
	    if(m != -1)
	    {
	      Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[0]),k);
	    }
	    else
	    {
	      Simulink::inName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Inport",s,"",0,"","",155, 485+65*count, 185, 505+65*count);
	      addBlockInfoInport(p,Simulink::inName,s);
	      Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	      Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[0]),k);
	      count++;
	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Outports of P
	  {
	    string s = getBlockInfoOutport(p->op.node[1],k);

	    if(s == "\"Out_ok\"")
	      continue;

	    Simulink::switchName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",840, 210+65*(k-1), 890, 240+65*(k-1));

	    Simulink::outName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1010, 215+65*(k-1), 1040, 235+65*(k-1));
	    addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	    Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,s,1);

	    s = s.replace(1,3,"In");
	    int m = getBlockInfoInport(p->op.node[1],s);
	    int n = getBlockInfoInport(p->op.node[0],s);
	    if(m != -1 || n !=1)
	    {
	      Simulink::addLine(tempSID,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	    }
	    else
	    {
	      // blkpos = getBlkPos();
	      // Simulink::randomName++;
	      // Simulink::addBlock(tempSID,"RandomNumber","\"Random\\nNumber"+to_string(Simulink::randomName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      // Simulink::addLine(tempSID,"\"Random\\nNumber"+to_string(Simulink::randomName)+"\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	      Simulink::inName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Inport",s,"",0,"","",715, 250+65*(k-1), 745, 270+65*(k-1));
	      addBlockInfoInport(p,Simulink::inName,s);
	      Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	      Simulink::addLine(tempSID,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	    }
	  }

	  Simulink::switchName++; //Add ok'
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",840, 120, 890, 150);
	  Simulink::outName++;
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",1010, 125, 1040, 145);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],"\"Out_ok\""),"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	  Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,"\"Out_ok\"",1);

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 14:      //Internal Choice "LI"
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;
	  
	  toSimulink1(p->op.node[0]);
	  toSimulink1(p->op.node[1]);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Inports of Q
	  {
	    if(getBlockInfoInport(p->op.node[1],k) == "\"In_ok\"")
	      continue;
	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[1],k),"",0,"","",80, 430+65*(k-1), 110, 450+65*(k-1));
	    addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[1],k));
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[1],k));
	    Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[1],k),1,getBlockInfoName(p->op.node[1]),k);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Inports of P
	  {
	    int count = 0;
	    if(getBlockInfoInport(p->op.node[0],k) == "\"In_ok\"")
	      continue;
	    string s = getBlockInfoInport(p->op.node[0],k);
	    int m = getBlockInfoInport(p->op.node[1],s);
	    if(m != -1)
	    {
	      Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[0]),k);
	    }
	    else
	    {
	      Simulink::inName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Inport",s,"",0,"","",80, 350+65*count, 110, 370+65*count);
	      addBlockInfoInport(p,Simulink::inName,s);
	      Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	      Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[0]),k);
	      count++;
	    }
	  }

	  // // blkpos = getBlkPos(); //Add switching block
	  // Simulink::randomName++;
	  // string key1 = "\"Random\\nNumber"+to_string(Simulink::randomName)+"\"";
	  // Simulink::addBlock(tempSID,"RandomNumber",key1,"",0,"","",545, 350, 575, 370);

	  // // blkpos = getBlkPos(); //Add a rate transition here to sample the random signal in order to produce same inport sampletime for switch blocks
	  // Simulink::randomName++;
	  // string key = "\"Rate Transition"+to_string(Simulink::randomName)+"\"";
	  // Simulink::addBlock(tempSID,"RateTransition",key,"\"0\"",0,"","",645, 350, 675, 370);
	  // Simulink::addLine(tempSID,key1,1,key,1);

	  Simulink::conName++;
	  // blkpos = getBlkPos();
	  string key = "\"Constant"+to_string(Simulink::conName)+"\"";
	  Simulink::addBlock(tempSID,"Constant",key,"\"round(rand())\"",0,"","",545, 350, 575, 370);

	  Simulink::inName++; //Link ok into P and Q
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",80, 105, 110, 125);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");

	  Simulink::conName++;
	  // blkpos = getBlkPos();
	  string blockzero = "\"Constant"+to_string(Simulink::conName)+"\"";
	  Simulink::addBlock(Simulink::subSysName,"Constant",blockzero,"0",0,"","",645, 145, 675, 165);
	  Simulink::relationalOptName++;
	  // blkpos = getBlkPos();
	  string blockrelation = "\"Relational\\nOperator"+to_string(Simulink::relationalOptName)+"\"";
	  Simulink::addBlock(Simulink::subSysName,"RelationalOperator",blockrelation,"",2,"\">\"","",725, 125, 755, 145);

	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd1,"",2,"\"AND\"","2",220, 110, 250, 130);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd2,"",2,"\"AND\"","2",220, 180, 250, 200);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockNot,"",1,"\"NOT\"","",220, 180, 250, 200);

	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd1,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd2,1);
	  Simulink::addLine(tempSID,key,1,blockrelation,1);
	  Simulink::addLine(tempSID,blockzero,1,blockrelation,2);
	  Simulink::addLine(tempSID,blockrelation,1,blockAnd1,2);
	  Simulink::addLine(tempSID,blockrelation,1,blockNot,1);
	  Simulink::addLine(tempSID,blockNot,1,blockAnd2,2);
	  Simulink::addLine(tempSID,blockAnd1,1,getBlockInfoName(p->op.node[0]),getBlockInfoInport(p->op.node[0],"\"In_ok\""));
	  Simulink::addLine(tempSID,blockAnd2,1,getBlockInfoName(p->op.node[1]),getBlockInfoInport(p->op.node[1],"\"In_ok\""));

	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Outports of Q and ok'
	  {
	    int count = 0;
	    string s = getBlockInfoOutport(p->op.node[1],k);

	    Simulink::switchName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",985, 100+65*(k-1), 1035, 130+65*(k-1));

	    Simulink::addLine(tempSID,key,1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);

	    Simulink::outName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1130, 105+65*(k-1), 1160, 125+65*(k-1));
	    addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	    Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,s,1);

	    int m = getBlockInfoOutport(p->op.node[0],s);
	    if(m != -1)
	    {
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	    }
	    else
	    {
	      // blkpos = getBlkPos();
	      // Simulink::randomName++;
	      // Simulink::addBlock(tempSID,"RandomNumber","\"Random\\nNumber"+to_string(Simulink::randomName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      // Simulink::addLine(tempSID,"\"Random\\nNumber"+to_string(Simulink::randomName)+"\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      s = s.replace(1,3,"In");
	      m = getBlockInfoInport(p->op.node[0],s);
	      int n = getBlockInfoInport(p->op.node[1],s);
	      if(m != -1 || n != -1)
	      {
		Simulink::addLine(tempSID,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
		Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      }
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",s,"",0,"","",80, 390+65*count, 110, 410+65*count);
		addBlockInfoInport(p,Simulink::inName,s);
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
		Simulink::addLine(tempSID,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
		Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
		count++;
	      }
	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Outports of P
	  {
	    int count = 0;
	    string s = getBlockInfoOutport(p->op.node[0],k);
	    int m = getBlockInfoOutport(p->op.node[1],s);

	    if(m == -1)
	    {
	      Simulink::switchName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",990, 435+65*(k-1), 1040, 465+65*(k-1));

	      Simulink::addLine(tempSID,key,1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);

	      Simulink::outName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1130, 440+65*(k-1), 1160, 460+65*(k-1));
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,s,1);
	      // blkpos = getBlkPos();
	      // Simulink::randomName++;
	      // Simulink::addBlock(tempSID,"RandomNumber","\"Random\\nNumber"+to_string(Simulink::randomName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      // Simulink::addLine(tempSID,"\"Random\\nNumber"+to_string(Simulink::randomName)+"\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      s = s.replace(1,3,"In");
	      m = getBlockInfoInport(p->op.node[0],s);
	      int n = getBlockInfoInport(p->op.node[1],s);
	      if(m != -1 || n !=1)
	      {
		Simulink::addLine(tempSID,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
		Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      }
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",s,"",0,"","",80, 400+65*count, 110, 420+65*count);
		addBlockInfoInport(p,Simulink::inName,s);
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
		Simulink::addLine(tempSID,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
		Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
		count++;
	      }
	    }
	  }

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 15:      //Sequential Composition ";"
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;
	  
	  toSimulink1(p->op.node[1]);
	  toSimulink1(p->op.node[0]);

	  // if(p->op.node[0]->op.name == ";" && p->op.node[1]->op.name == "?") // Test for lack of inports&outports in Assignment
	  // {
	  //   cout<<"FUCK ----"<<endl;
	  //   for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++)
	  //     cout<<k<<"\t"<<getBlockInfoOutport(p->op.node[0],k)<<endl;
	  //   cout<<"FUCK ~~~~"<<endl;
	  //   for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++)
	  //     cout<<k<<"\t"<<getBlockInfoInport(p->op.node[1],k)<<endl;
	  // }
	  // if(p->op.node[0]->op.node[1]->op.name == "?")
	  // {
	  //   cout<<"FUCK ----"<<endl;
	  //   for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++)
	  //     cout<<k<<"\t"<<getBlockInfoOutport(p->op.node[0],k)<<endl;
	  //   cout<<"FUCK ~~~~"<<endl;
	  //   for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++)
	  //     cout<<k<<"\t"<<getBlockInfoInport(p->op.node[1],k)<<endl;
	  //   cout<<"FUCK ^^^^"<<endl;
	  //   for(k=1;getBlockInfoInport(p->op.node[1]->op.node[1],k)!="";k++)
	  //     cout<<k<<"\t"<<getBlockInfoInport(p->op.node[1]->op.node[1],k)<<endl;
	  // }

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Inports of P (including ok)
	  {
	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[0],k),"",0,"","",165, 215+65*(k-1), 195, 235+65*(k-1));
	    addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[0],k));
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[0],k));
	    Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[0],k),1,getBlockInfoName(p->op.node[0]),k);
	  }

	  int count1 = 0;
	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Draw lines from P to Q in terms of P;Q
	  {
	    string s = getBlockInfoInport(p->op.node[1],k);
	    s = s.replace(1,2,"Out");
	    int m = getBlockInfoOutport(p->op.node[0],s);
	    if(m != -1)
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,getBlockInfoName(p->op.node[1]),k);
	    else
	    {
	      s = s.replace(1,3,"In");
	      m = getBlockInfoInport(p->op.node[0],s);
	      if(m != -1)
		Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",s,"",0,"","",675, 215+65*count1, 705, 235+65*count1);
		addBlockInfoInport(p,Simulink::inName,s);
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
		Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);
		count1++;
	      }
	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Outports of P
	  {
	    string s = getBlockInfoOutport(p->op.node[0],k);
	    if(s == "\"Out_ok\"")
	      continue;
	    // int m = getBlockInfoOutport(p->op.node[1],s);
	    s = s.replace(1,3,"In");
	    int m = getBlockInfoInport(p->op.node[1],s);
	    s = s.replace(1,2,"Out");
	    if(m == -1)
	    {
	      Simulink::outName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",580, 215+65*(k-1), 610, 235+65*(k-1));
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,s,1);
	    }
	    else
	    {
	      // // Simulink::switchName++; //Switch outside
	      // // blkpos = getBlkPos();
	      // // Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+20,blkpos.y2+10);

	      // Simulink::outName++;
	      // blkpos = getBlkPos();
	      // Simulink::addBlock(tempSID,"Outport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      // addBlockInfoOutport(p,Simulink::outName,s);
	      // Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);

	      // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,s,1);
	      // // Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,s,1);
	      // // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      // // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),m,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      // // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],"\"Out_ok\""),"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Outports of Q (including ok')
	  {
	    string s = getBlockInfoOutport(p->op.node[1],k);
	    // Simulink::switchName++;
	    // blkpos = getBlkPos();
	    // Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+20,blkpos.y2+10);

	    Simulink::outName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1125, 215+65*(k-1), 1155, 235+65*(k-1));
	    addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);

	    Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,s,1);
	    // Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,s,1);
	    // Simulink::addLine(tempSID,s.replace(1,3,"In"),1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	    // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	    // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],"\"Out_ok\""),"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	    s = s.replace(1,2,"Out");
	  }

	  // Simulink::outName++; //Add ok'
	  // blkpos = getBlkPos();
	  // Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  // addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  // Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");
	  // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],"\"Out_ok\""),"\"Out_ok\"",1);
	  // Simulink::logicalOptName++;
	  // blkpos = getBlkPos();
	  // Simulink::addBlock(tempSID,"Logic","\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"","",p->op.num,"\"AND\"",to_string(p->op.num),blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  // Simulink::addLine(tempSID,"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",1,"\"Out_ok\"",1);
	  // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],"\"Out_ok\""),"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",1);
	  // Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],"\"Out_ok\""),"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",2);

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 16:      //Recursion "REP"
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  toSimulink1(p->op.node[0]);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  Simulink::inName++; //Add ok
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",215,60,245,80);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");

	  Simulink::outName++; //Add ok'
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",1155,70,1185,90);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++; //Compute n,ok,ok' 
	  string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd1,"",2,"\"AND\"","2",880, 62, 910, 93);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd2,"",2,"\"AND\"","2",880, 117, 910, 148);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd3 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd3,"",2,"\"AND\"","2",301, 625, 334, 655);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockNot1,"",1,"\"NOT\"","",965, 169, 995, 201);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockOr1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockOr1,"",2,"\"OR\"","2",327, 470, 358, 500);

	  Simulink::relationalOptName++;
	  // blkpos = getBlkPos();
	  string blockGre1 = "\"Relational\\nOperator"+to_string(Simulink::relationalOptName)+"\"";
	  Simulink::addBlock(Simulink::subSysName,"RelationalOperator",blockGre1,"",2,"\">\"","",415, 427, 445, 458);
	  Simulink::relationalOptName++;
	  // blkpos = getBlkPos();
	  string blockEqu1 = "\"Relational\\nOperator"+to_string(Simulink::relationalOptName)+"\"";
	  Simulink::addBlock(Simulink::subSysName,"RelationalOperator",blockEqu1,"",2,"\"==\"","",415, 367, 445, 398);

	  // blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay1,"\"0\"",0,"","",965, 238, 1000, 272);
	  // blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay2 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay2,"\"0\"",0,"","",388, 215, 422, 250);
	  // blkpos = getBlkPos();
	  // Simulink::delayName++;
	  // string blockDelay3 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  // Simulink::addBlock(tempSID,"UnitDelay",blockDelay3,"\"1\"",0,"","",328, 545, 362, 580);
	  // blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay4 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay4,"\"0\"",0,"","",680, 117, 710, 148);

	  // blkpos = getBlkPos();
	  Simulink::sumName++;
	  string blockSum1 = "\"Add"+to_string(Simulink::sumName)+"\"";
	  Simulink::addBlock(tempSID,"Sum",blockSum1,"",2,"","++",480, 215, 520, 245);
	  // blkpos = getBlkPos();
	  Simulink::productName++;
	  string blockPro1 = "\"Divide"+to_string(Simulink::productName)+"\"";
	  Simulink::addBlock(tempSID,"Product",blockPro1,"",2,"","**",515, 302, 545, 333);

	  Simulink::conName++;
	  // blkpos = getBlkPos();
	  string blockCon1 = "\"Constant"+to_string(Simulink::conName)+"\"";
	  Simulink::addBlock(tempSID,"Constant",blockCon1,"\"rand()*10000\"",0,"","",415, 525, 445, 545);

	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd1,1);
	  Simulink::addLine(tempSID,blockGre1,1,blockAnd1,2);
	  Simulink::addLine(tempSID,blockAnd1,1,"\"Out_ok\"",1);
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],"\"Out_ok\""),blockDelay1,1);
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],"\"Out_ok\""),blockAnd2,2);
	  Simulink::addLine(tempSID,blockDelay1,1,blockNot1,1);
	  Simulink::addLine(tempSID,blockNot1,1,blockAnd2,1);
	  // Simulink::addLine(tempSID,blockAnd2,1,blockSum1,2);
	  Simulink::addLine(tempSID,blockAnd2,1,blockDelay4,1);
	  Simulink::addLine(tempSID,blockDelay4,1,blockSum1,2);
	  Simulink::addLine(tempSID,blockDelay2,1,blockSum1,1);
	  // Simulink::addLine(tempSID,blockSum1,1,blockDelay2,1);
	  Simulink::addLine(tempSID,blockPro1,1,blockDelay2,1);
	  Simulink::addLine(tempSID,blockSum1,1,blockPro1,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockPro1,2);
	  Simulink::addLine(tempSID,blockPro1,1,blockEqu1,2);
	  Simulink::addLine(tempSID,blockDelay2,1,blockEqu1,1);
	  Simulink::addLine(tempSID,blockEqu1,1,blockOr1,1);
	  Simulink::addLine(tempSID,blockPro1,1,blockGre1,1);
	  Simulink::addLine(tempSID,blockCon1,1,blockGre1,2);
	  Simulink::addLine(tempSID,blockGre1,1,blockOr1,2);
	  // Simulink::addLine(tempSID,blockOr1,1,blockDelay3,1);
	  // Simulink::addLine(tempSID,blockDelay3,1,blockAnd3,2);
	  Simulink::addLine(tempSID,blockOr1,1,blockAnd3,2);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd3,1);
	  Simulink::addLine(tempSID,blockAnd3,1,getBlockInfoName(p->op.node[0]),getBlockInfoInport(p->op.node[0],"\"In_ok\""));

	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Outports of P
	  {
	    string s = getBlockInfoOutport(p->op.node[0],k);
	    if(s == "\"Out_ok\"")
	      continue;
	    Simulink::outName++;
	    blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	    addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	    Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,s,1);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Inports of P
	  {
	    string s = getBlockInfoInport(p->op.node[0],k);
	    if(s == "\"In_ok\"")
	      continue;
	    Simulink::inName++;
	    blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	    addBlockInfoInport(p,Simulink::inName,s);
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	    s = s.replace(1,2,"Out");
	    int m = getBlockInfoOutport(p->op.node[0],s);
	    s = s.replace(1,3,"In");
	    if(m == -1)
	      Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[0]),k);
	    else
	    {
	      // blkpos = getBlkPos();
	      Simulink::delayName++;
	      Simulink::addBlock(tempSID,"UnitDelay","\"Unit Delay"+to_string(Simulink::delayName)+"\"","\"0\"",0,"","",850,453+(k-1)*40,885,487+(k-1)*40);
	      // blkpos = getBlkPos();
	      Simulink::switchName++;
	      Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",975,490+(k-1)*40,1025,530+(k-1)*40);
	      
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,"\"Unit Delay"+to_string(Simulink::delayName)+"\"",1);
	      Simulink::addLine(tempSID,"\"Unit Delay"+to_string(Simulink::delayName)+"\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      Simulink::addLine(tempSID,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      Simulink::addLine(tempSID,blockPro1,1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	      Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,getBlockInfoName(p->op.node[0]),k);
	    }
	  }

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 17:      //Communication Event "?"
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  Simulink::inName++; //Add ok
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");

	  Simulink::inName++; //Add ready
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ready_"+p->op.node[0]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ready_"+p->op.node[0]->index+"\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ready_"+p->op.node[0]->index+"\"");

	  Simulink::outName++; //Add ok'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  Simulink::outName++; //Add ready'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"");


	  blkpos = getBlkPos(); //Compute ok' and ready'
	  Simulink::logicalOptName++;
	  string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd1,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos(); 
	  Simulink::logicalOptName++;
	  string blockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd2,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd3 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd3,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd4 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd4,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockNot,"",1,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockOr = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockOr,"",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay1,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay2 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay2,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::addLine(tempSID,"\"In_ready_"+p->op.node[0]->index+"\"",1,blockAnd1,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd1,2);
	  Simulink::addLine(tempSID,blockAnd1,1,blockDelay1,1);
	  Simulink::addLine(tempSID,blockDelay1,1,blockAnd3,1);
	  // Simulink::addLine(tempSID,blockAnd1,1,blockAnd3,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd3,2);
	  Simulink::addLine(tempSID,blockAnd3,1,blockOr,1);
	  Simulink::addLine(tempSID,blockOr,1,"\"Out_ok\"",1);
	  Simulink::addLine(tempSID,blockOr,1,blockNot,1);
	  // Simulink::addLine(tempSID,"\"In_ok\"",1,blockNot,1);
	  Simulink::addLine(tempSID,blockOr,1,blockDelay2,1);
	  Simulink::addLine(tempSID,blockDelay2,1,blockAnd4,2);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd4,1);
	  Simulink::addLine(tempSID,blockAnd4,1,blockOr,2);
	  Simulink::addLine(tempSID,blockNot,1,blockAnd2,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd2,2);
	  Simulink::addLine(tempSID,blockAnd2,1,"\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"",1);

	  Simulink::inName++; //Add x
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_"+p->op.node[1]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_"+p->op.node[1]->index+"\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_"+p->op.node[1]->index+"\"");
	  Simulink::outName++; //Add x'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_"+p->op.node[1]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_"+p->op.node[1]->index+"\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_"+p->op.node[1]->index+"\"");

	  Simulink::inName++; //Add e from the sender
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_"+p->op.node[0]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_"+p->op.node[0]->index+"\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_"+p->op.node[0]->index+"\"");

	  Simulink::switchName++; //Compute x'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+20,blkpos.y2+10);
	  blkpos = getBlkPos();
	  Simulink::productName++;
	  string blockpro1 = "\"Divide"+to_string(Simulink::productName)+"\"";
	  Simulink::addBlock(tempSID,"Product",blockpro1,"",2,"","**",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::productName++;
	  string blockpro2 = "\"Divide"+to_string(Simulink::productName)+"\"";
	  Simulink::addBlock(tempSID,"Product",blockpro2,"",2,"","**",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockNot1,"",1,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::sumName++;
	  string blocksum1 = "\"Add"+to_string(Simulink::sumName)+"\"";
	  Simulink::addBlock(tempSID,"Sum",blocksum1,"",2,"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay3 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay3,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay4 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay4,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::addLine(tempSID,"\"In_"+p->op.node[0]->index+"\"",1,blockpro1,1);
	  Simulink::addLine(tempSID,blockNot1,1,blockpro1,2);
	  Simulink::addLine(tempSID,blockpro1,1,blocksum1,1);
	  Simulink::addLine(tempSID,blockpro2,1,blocksum1,2);
	  Simulink::addLine(tempSID,blocksum1,1,blockDelay3,1);
	  Simulink::addLine(tempSID,blockDelay3,1,blockpro2,1);
	  Simulink::addLine(tempSID,blockOr,1,blockpro2,2);
	  // Simulink::addLine(tempSID,blockOr,1,blockNot1,1);
	  Simulink::addLine(tempSID,blockOr,1,blockDelay4,1);
	  Simulink::addLine(tempSID,blockDelay4,1,blockNot1,1);
	  Simulink::addLine(tempSID,blocksum1,1,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	  Simulink::addLine(tempSID,blockOr,1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	  Simulink::addLine(tempSID,"\"In_"+p->op.node[1]->index+"\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	  Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,"\"Out_"+p->op.node[1]->index+"\"",1);

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 18:      //Communication Event "!"
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  Simulink::inName++; //Add ok
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");

	  Simulink::inName++; //Add ready
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ready_"+p->op.node[0]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ready_"+p->op.node[0]->index+"\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ready_"+p->op.node[0]->index+"\"");

	  Simulink::outName++; //Add ok'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  Simulink::outName++; //Add ready'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"");


	  blkpos = getBlkPos(); //Compute ok' and ready'
	  Simulink::logicalOptName++;
	  string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd1,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd2,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd3 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd3,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd4 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd4,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockNot,"",1,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockOr = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockOr,"",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay1,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay2 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay2,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::addLine(tempSID,"\"In_ready_"+p->op.node[0]->index+"\"",1,blockAnd1,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd1,2);
	  Simulink::addLine(tempSID,blockAnd1,1,blockDelay1,1);
	  Simulink::addLine(tempSID,blockDelay1,1,blockAnd3,1);
	  // Simulink::addLine(tempSID,blockAnd1,1,blockAnd3,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd3,2);
	  Simulink::addLine(tempSID,blockAnd3,1,blockOr,1);
	  Simulink::addLine(tempSID,blockOr,1,"\"Out_ok\"",1);
	  Simulink::addLine(tempSID,blockOr,1,blockNot,1);
	  // Simulink::addLine(tempSID,"\"In_ok\"",1,blockNot,1);
	  Simulink::addLine(tempSID,blockOr,1,blockDelay2,1);
	  Simulink::addLine(tempSID,blockDelay2,1,blockAnd4,2);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd4,1);
	  Simulink::addLine(tempSID,blockAnd4,1,blockOr,2);
	  Simulink::addLine(tempSID,blockNot,1,blockAnd2,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd2,2);
	  Simulink::addLine(tempSID,blockAnd2,1,"\"Out_ready_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"",1);

	  Simulink::inName++; //Add e
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_"+p->op.node[1]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_"+p->op.node[1]->index+"\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_"+p->op.node[1]->index+"\"");
	  Simulink::outName++; //Add e'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_"+p->op.node[1]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_"+p->op.node[1]->index+"\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_"+p->op.node[1]->index+"\"");

	  Simulink::outName++; //Add e' for the receiver
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"");

	  Simulink::addLine(tempSID,"\"In_"+p->op.node[1]->index+"\"",1,"\"Out_"+p->op.node[1]->index+"\"",1);
	  Simulink::addLine(tempSID,"\"In_"+p->op.node[1]->index+"\"",1,"\"Out_"+p->op.node[0]->index+"_"+to_string(tempSID)+"\"",1);

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 19:      //Preemption "[[>"
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  // toSimulink1(p->op.node[0]);
	  // toSimulink1(p->op.node[1]);

	  /*************************************************<F=0 &&(B & ~Ready)>*************************************************/

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p->op.node[0],"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  int tempSID1 = Simulink::subSysName;

	  DifferentialEquations dequ(p->op.node[0]->op.node[0]);
	  dequ.toSimulink(dequ.getRoot(),tempSID1);
	  BoolExpression bexp(p->op.node[0]->op.node[1]);
	  bexp.toSimulink(bexp.getRoot(),tempSID1);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  Simulink::inName++; //Add Ready
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID1,"Inport","\"In_Ready\"","",0,"","",75, 571, 105, 591);
	  addBlockInfoInport(p->op.node[0],Simulink::inName,"\"In_Ready\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID1)+"\"",Simulink::inName,"\"In_Ready\"");
	  
	  Simulink::logicalOptName++; //Compute B & ~Ready
	  string blockNotforReady = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID1,"Logic",blockNotforReady,"",1,"\"NOT\"","",880, 571, 920, 599);
	  Simulink::addLine(tempSID1,"\"In_Ready\"",1,blockNotforReady,1);
	  Simulink::logicalOptName++;
	  string blockAndforReady = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID1,"Logic",blockAndforReady,"",2,"\"AND\"","2",990, 481, 1020, 514);

	  // blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID1,"UnitDelay",blockDelay1,"\"1\"",0,"","",380, 95, 410, 115);

	  Simulink::addLine(tempSID1,getBlockInfoName(p->op.node[0]->op.node[1]),1,blockAndforReady,1);
	  Simulink::addLine(tempSID1,blockNotforReady,1,blockDelay1,1);
	  Simulink::addLine(tempSID1,blockDelay1,1,blockAndforReady,2);

	  Simulink::inName++; //Add ok
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID1,"Inport","\"In_ok\"","",0,"","",75, 150, 105, 170);
	  addBlockInfoInport(p->op.node[0],Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID1)+"\"",Simulink::inName,"\"In_ok\"");
	  Simulink::outName++; //Add ok'
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID1,"Outport","\"Out_ok\"","",0,"","",1235, 70, 1265, 90);
	  addBlockInfoOutport(p->op.node[0],Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID1)+"\"",Simulink::outName,"\"Out_ok\"");

	  // blkpos = getBlkPos();
	  // Simulink::logicalOptName++;
	  // string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  // Simulink::addBlock(tempSID1,"Logic",blockAnd1,"",2,"\"AND\"",to_string(p->op.node[0]->op.num),blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID1,"Logic",blockAnd2,"",2,"\"AND\"",to_string(p->op.node[0]->op.num),465, 225, 495, 245);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd3 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID1,"Logic",blockAnd3,"",2,"\"AND\"",to_string(p->op.node[0]->op.num),655, 70, 685, 90);
	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID1,"Logic",blockNot,"",1,"\"NOT\"","",380, 30, 410, 50);

	  // blkpos = getBlkPos();
	  // Simulink::delayName++;
	  // string blockDelay2 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  // Simulink::addBlock(tempSID1,"UnitDelay",blockDelay2,"\"1\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  // // Simulink::addLine(tempSID1,getBlockInfoName(p->op.node[0]->op.node[1]),1,blockDelay1,1); //Break the algebraic loop
	  // Simulink::addLine(tempSID1,blockAndforReady,1,blockDelay1,1); //Break the algebraic loop
	  // // Simulink::addLine(tempSID1,blockDelay1,1,blockAnd1,1);
	  // Simulink::addLine(tempSID1,blockDelay1,1,blockAnd2,2);
	  Simulink::addLine(tempSID1,blockAndforReady,1,blockAnd2,2);

	  // Simulink::addLine(tempSID1,blockAnd1,1,blockDelay2,1);
	  // Simulink::addLine(tempSID1,blockDelay2,1,blockAnd1,2);

	  Simulink::addLine(tempSID1,"\"In_ok\"",1,blockAnd2,1);
	  // Simulink::addLine(tempSID1,blockAnd1,1,blockAnd2,2);
	  // Simulink::addLine(tempSID1,blockAnd1,1,getBlockInfoName(p->op.node[0]->op.node[0]),'e');
	  // Simulink::addLine(tempSID1,blockAnd2,1,blockAnd1,1);
	  // Simulink::addLine(tempSID1,blockAnd2,1,getBlockInfoName(p->op.node[0]->op.node[0]),'e'); //enableport is no more needed, fixed on Feb 8, 2015
	  Simulink::addLine(tempSID1,blockAnd2,1,getBlockInfoName(p->op.node[0]->op.node[0]),getBlockInfoInport(p->op.node[0]->op.node[0],"\"In_enable\""));

	  // Simulink::addLine(tempSID1,blockDelay1,1,blockNot,1);
	  Simulink::addLine(tempSID1,blockAndforReady,1,blockNot,1);
	  Simulink::addLine(tempSID1,"\"In_ok\"",1,blockAnd3,1);
	  Simulink::addLine(tempSID1,blockNot,1,blockAnd3,2);
	  Simulink::addLine(tempSID1,blockAnd3,1,"\"Out_ok\"",1);

	  for(k=1;getBlockInfoInport(p->op.node[0]->op.node[1],k)!="";k++) //Draw lines from F to B in terms of <F&&B>
	  {
	    int count = 0;
	    string s= getBlockInfoInport(p->op.node[0]->op.node[1],k);
	    s = s.replace(1,2,"Out");
	    int m = getBlockInfoOutport(p->op.node[0]->op.node[0],s);
	    if(m != -1)
	      Simulink::addLine(tempSID1,getBlockInfoName(p->op.node[0]->op.node[0]),m,getBlockInfoName(p->op.node[0]->op.node[1]),k);
	    else
	    {
	      s = s.replace(1,3,"In");
	      m = getBlockInfoInport(p->op.node[0]->op.node[0],s);
	      if(m != -1)
		Simulink::addLine(tempSID1,s,1,getBlockInfoName(p->op.node[0]->op.node[1]),k);
	      else
	      {
		Simulink::inName++;
		count++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID1,"Inport",s,"",0,"","",655, 475+65*count, 685, 495+65*count);
		addBlockInfoInport(p->op.node[0],Simulink::inName,s);
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID1)+"\"",Simulink::inName,s);
		Simulink::addLine(tempSID1,s,1,getBlockInfoName(p->op.node[0]->op.node[1]),k);
	      }
	    }
	  }

	  // for(k=1;getBlockInfoOutport(p->op.node[0]->op.node[0],k)!="";k++) //Plug a multiple-axi-Scope here
	  // {}
	  // Simulink::scopeName++;
	  // blkpos = getBlkPos();
	  // Simulink::addBlock(tempSID1,"Scope","\"Scope"+to_string(Simulink::scopeName)+"\"","",k-1,"","",blkpos.x1,blkpos.y1,blkpos.x2+10,blkpos.y2+30);
	  for(k=1;getBlockInfoOutport(p->op.node[0]->op.node[0],k)!="";k++) //Add outports
	  {
	    Simulink::outName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID1,"Outport",getBlockInfoOutport(p->op.node[0]->op.node[0],k),"",0,"","",1235, 140+65*k, 1265, 160+65*k);
	    addBlockInfoOutport(p->op.node[0],Simulink::outName,getBlockInfoOutport(p->op.node[0]->op.node[0],k));
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID1)+"\"",Simulink::outName,getBlockInfoOutport(p->op.node[0]->op.node[0],k));
	    Simulink::addLine(tempSID1,getBlockInfoName(p->op.node[0]->op.node[0]),k,getBlockInfoOutport(p->op.node[0]->op.node[0],k),1);

	    // Simulink::addLine(tempSID1,getBlockInfoName(p->op.node[0]->op.node[0]),k,"\"Scope"+to_string(Simulink::scopeName)+"\"",k);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[0]->op.node[0],k)!="";k++) //Add inports
	  {
	    if(getBlockInfoInport(p->op.node[0]->op.node[0],k) == "\"In_enable\"")
	      continue;
	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID1,"Inport",getBlockInfoInport(p->op.node[0]->op.node[0],k),"",0,"","",75, 330+65*k, 105, 350+65*k);
	    addBlockInfoInport(p->op.node[0],Simulink::inName,getBlockInfoInport(p->op.node[0]->op.node[0],k));
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID1)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[0]->op.node[0],k));
	    Simulink::addLine(tempSID1,getBlockInfoInport(p->op.node[0]->op.node[0],k),1,getBlockInfoName(p->op.node[0]->op.node[0]),k);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[0]->op.node[0],k)!="";k++) //Switch inport&outport signal according to ok
	  {
	    if(getBlockInfoInport(p->op.node[0]->op.node[0],k) == "\"In_enable\"")
	      continue;
	    string si = getBlockInfoInport(p->op.node[0]->op.node[0],k);
	    string so = si.replace(1,2,"Out");
	    si = getBlockInfoInport(p->op.node[0]->op.node[0],k);

	    Simulink::switchName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID1,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",1085, 135+65*k, 1135, 165+65*k);

	    Simulink::breakLine(tempSID1,"\"Switch"+to_string(Simulink::switchName)+"\"",1,1,so,1);
	    Simulink::addLine(tempSID1,si,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	    Simulink::addLine(tempSID1,"\"In_ok\"",1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	  }

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);

	  /*************************************************<F=0 &&(B & ~Ready)>*************************************************/

	  /**************************************************Ready -> [[(io->Q)**************************************************/

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+200,blkpos.y2+124);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  // setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  int tempSID2 = Simulink::subSysName;
	  
	  toSimulink1(p->op.node[1]);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  string blockAndforOkP = "";
	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Inports of P (including ok)
	  {
	    int count = 0;
	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID2,"Inport",getBlockInfoInport(p->op.node[1],k),"",0,"","",155, 135+65*(k-1), 185, 155+65*(k-1));
	    // addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[1],k));
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID2)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[1],k));
	    if(getBlockInfoInport(p->op.node[1],k) == "\"In_ok\"") //ok_P = ok&Ready
	    {
	      Simulink::logicalOptName++;
	      blockAndforOkP = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	      Simulink::addBlock(tempSID2,"Logic",blockAndforOkP,"",2,"\"AND\"","2",225, 160+65*(k-1), 255, 180+65*(k-1));
	      Simulink::addLine(tempSID2,"\"In_ok\"",1,blockAndforOkP,1);
	      //A line from Ready to inport-2 of this And block left to be drew 
	      Simulink::addLine(tempSID2,blockAndforOkP,1,getBlockInfoName(p->op.node[1]),k);
	    }
	    else
	      Simulink::addLine(tempSID2,getBlockInfoInport(p->op.node[1],k),1,getBlockInfoName(p->op.node[1]),k);

	    string s = getBlockInfoInport(p->op.node[1],k);
	    if(s.find("ready") < s.length() || s.find("ch")<s.length() || s.find("ok") < s.length())
	      continue;

	    s = s.replace(1,2,"Out");
	    int m = getBlockInfoOutport(p->op.node[1],s);
	    if(m == -1)
	    {
	      Simulink::outName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID2,"Outport",s,"",0,"","",1010, 485+65*count, 1040, 505+65*count);
	      // addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID2)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID2,s.replace(1,3,"In"),1,s,1);
	      s = s.replace(1,2,"Out");
	      count++;
	    }
	  }

	  // string blockKey = getBlockInfoName(p->op.node[1]);
	  // int portKey = getBlockInfoOutport(p->op.node[1],"\"Out_Ready\"");

	  Simulink::logicalOptName++;
	  string blockAnd = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\""; //Keep Ready
	  Simulink::addBlock(tempSID2,"Logic",blockAnd,"",2,"\"AND\"","2",451, 545, 484, 575);
	  Simulink::logicalOptName++;
	  string blockOr = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID2,"Logic",blockOr,"",2,"\"OR\"","2",525, 506, 555, 539);
	  Simulink::delayName++;
	  string blockDelay = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID2,"UnitDelay",blockDelay,"\"0\"",0,"","",525, 610, 555, 630);

	  Simulink::addLine(tempSID2,blockAnd,1,blockOr,2);
	  Simulink::addLine(tempSID2,blockOr,1,blockDelay,1);
	  Simulink::addLine(tempSID2,blockDelay,1,blockAnd,2);
	  Simulink::addLine(tempSID2,"\"In_ok\"",1,blockAnd,1);

	  string blockKey = blockOr;
	  int portKey = 1;

	  // Simulink::delayName++;
	  // string blockDelayforOkP = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  // Simulink::addBlock(tempSID2,"UnitDelay",blockDelayforOkP,"\"0\"",0,"","",295, 185, 325, 205);

	  Simulink::addLine(tempSID2,blockKey,portKey,blockAndforOkP,2); //ok_P = ok&Ready
	  // Simulink::addLine(tempSID2,blockKey,portKey,blockDelayforOkP,1); //ok_P = ok&d(Ready)
	  // Simulink::addLine(tempSID2,blockDelayforOkP,1,blockAndforOkP,2);

	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Outports of P
	  {
	    string s = getBlockInfoOutport(p->op.node[1],k);

	    if(s == "\"Out_Ready\"")
	    {
	      Simulink::outName++;
	      Simulink::addBlock(tempSID2,"Outport",s,"",0,"","",1010, 215+65*(k-1), 1040, 235+65*(k-1));
	      // addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID2)+"\"",Simulink::outName,s);

	      Simulink::addLine(tempSID2,getBlockInfoName(p->op.node[1]),k,blockOr,1);
	      Simulink::addLine(tempSID2,blockOr,1,s,1);
	      continue;
	    }

	    if(s.find("ready") < s.length() || s.find("ch")<s.length())
	    {
	      Simulink::outName++;
	      Simulink::addBlock(tempSID2,"Outport",s,"",0,"","",1010, 215+65*(k-1), 1040, 235+65*(k-1));
	      // addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID2)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID2,getBlockInfoName(p->op.node[1]),k,s,1);
	      continue;
	    }

	    Simulink::switchName++;
	    Simulink::addBlock(tempSID2,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",840, 210+65*(k-1), 890, 240+65*(k-1));

	    Simulink::outName++;
	    Simulink::addBlock(tempSID2,"Outport",s,"",0,"","",1010, 215+65*(k-1), 1040, 235+65*(k-1));
	    // addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID2)+"\"",Simulink::outName,s);
	    Simulink::addLine(tempSID2,"\"Switch"+to_string(Simulink::switchName)+"\"",1,s,1);

	    s = s.replace(1,3,"In");
	    int m = getBlockInfoInport(p->op.node[1],s);
	    if(m != -1)
	    {
	      Simulink::addLine(tempSID2,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      Simulink::addLine(tempSID2,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      Simulink::addLine(tempSID2,blockKey,portKey,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	    }
	    else
	    {
	      Simulink::inName++;
	      Simulink::addBlock(tempSID2,"Inport",s,"",0,"","",715, 250+65*(k-1), 745, 270+65*(k-1));
	      // addBlockInfoInport(p,Simulink::inName,s);
	      Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID2)+"\"",Simulink::inName,s);
	      Simulink::addLine(tempSID2,s,1,"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      Simulink::addLine(tempSID2,getBlockInfoName(p->op.node[1]),k,"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      Simulink::addLine(tempSID2,blockKey,portKey,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	    }
	  }

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);

	  /**************************************************Ready -> [[(io->Q)**************************************************/

	  /*******************************************************<> ; ->********************************************************/

	  setBlockInfoName(p->op.node[1],"\"SubSystem"+to_string(tempSID2)+"\"");

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Inports of P (including ok)
	  {
	    if(getBlockInfoInport(p->op.node[0],k) == "\"In_Ready\"")
	      continue;
	    Simulink::inName++;
	    Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[0],k),"",0,"","",165, 215+65*(k-1), 195, 235+65*(k-1));
	    addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[0],k));
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[0],k));
	    Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[0],k),1,getBlockInfoName(p->op.node[0]),k);
	  }

	  int count1 = 0;
	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Draw lines from P to Q in terms of P;Q
	  {
	    string s = getBlockInfoInport(p->op.node[1],k);
	    s = s.replace(1,2,"Out");
	    int m = getBlockInfoOutport(p->op.node[0],s);
	    if(m != -1)
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,getBlockInfoName(p->op.node[1]),k);
	    else
	    {
	      s = s.replace(1,3,"In");
	      m = getBlockInfoInport(p->op.node[0],s);
	      if(m != -1)
		Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",s,"",0,"","",675, 215+65*count1, 705, 235+65*count1);
		addBlockInfoInport(p,Simulink::inName,s);
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
		Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);
		count1++;
	      }
	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Outports of P
	  {
	    string s = getBlockInfoOutport(p->op.node[0],k);
	    if(s == "\"Out_ok\"")
	      continue;
	    s = s.replace(1,3,"In");
	    int m = getBlockInfoInport(p->op.node[1],s);
	    s = s.replace(1,2,"Out");
	    if(m == -1)
	    {
	      Simulink::outName++;
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",580, 215+65*(k-1), 610, 235+65*(k-1));
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,s,1);
	    }
	    else
	    {

	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Outports of Q (including ok')
	  {
	    string s = getBlockInfoOutport(p->op.node[1],k);
	    if(s == "\"Out_Ready\"")
	    {
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,getBlockInfoName(p->op.node[0]),getBlockInfoInport(p->op.node[0],"\"In_Ready\""));
	      continue;
	    }
	    Simulink::outName++;
	    Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1125, 215+65*(k-1), 1155, 235+65*(k-1));
	    addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);

	    Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,s,1);
	    s = s.replace(1,2,"Out");
	  }

	  /*******************************************************<> ; ->********************************************************/

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 20:      //External Choice "[["
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  toSimulink1(p->op.node[0]);
	  toSimulink1(p->op.node[1]);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  Simulink::inName++; //Add ok
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");

	  Simulink::outName++; //Add ok'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  Simulink::outName++; //Add Ready'
	  blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_Ready\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_Ready\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_Ready\"");

	  blkpos = getBlkPos(); //Compute Ready'
	  Simulink::logicalOptName++;
	  string blockor0 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockor0,"",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  Simulink::addLine(tempSID,blockor0,1,"\"Out_Ready\"",1);

	  string blockReady;
	  int portReady;

	  string pblockReady; //re of Q, used when computing ok_P
	  int pportReady;

	  if(getBlockInfoOutport(p->op.node[0],"\"Out_Ready\"") == -1)
	  {
	    for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++)
	    {
	      string s = getBlockInfoInport(p->op.node[0],k);
	      if(s.find("ready") < s.length())
	      {
		Simulink::addLine(tempSID,s,1,blockor0,1);
		blockReady = s;
		portReady = 1;
		break;
	      }
	    }
	  }
	  else
	  {
	    blockReady = getBlockInfoName(p->op.node[0]);
	    portReady = getBlockInfoOutport(p->op.node[0],"\"Out_Ready\"");
	    Simulink::addLine(tempSID,blockReady,portReady,blockor0,1);
	  }
	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++)
	  {
	    string s = getBlockInfoInport(p->op.node[1],k);
	    if(s.find("ready") < s.length())
	    {
	      Simulink::addLine(tempSID,s,1,blockor0,2);
	      pblockReady = s;
	      pportReady = 1;
	      break;
	    }
	  }

	  blkpos = getBlkPos(); //Compute ok'
	  Simulink::logicalOptName++;
	  Simulink::addBlock(tempSID,"Logic","\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"","",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],"\"Out_ok\""),"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",1);
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],"\"Out_ok\""),"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",2);
	  Simulink::addLine(tempSID,"\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"",1,"\"Out_ok\"",1);

	  // blkpos = getBlkPos(); //Compute ok for Q
	  // Simulink::randomName++;
	  // string key1 = "\"Random\\nNumber"+to_string(Simulink::randomName)+"\"";
	  // Simulink::addBlock(tempSID,"RandomNumber",key1,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  // // blkpos = getBlkPos(); //Add a rate transition here to sample the random signal in order to produce same inport sampletime for switch blocks
	  // Simulink::randomName++;
	  // string key = "\"Rate Transition"+to_string(Simulink::randomName)+"\"";
	  // Simulink::addBlock(tempSID,"RateTransition",key,"\"0\"",0,"","",blkpos.x1+100,blkpos.y1,blkpos.x2+100,blkpos.y2);

	  // Simulink::addLine(tempSID,key1,1,key,1);

	  Simulink::conName++; //Compute ok for Q
	  blkpos = getBlkPos();
	  string key = "\"Constant"+to_string(Simulink::conName)+"\"";
	  Simulink::addBlock(tempSID,"Constant",key,"\"round(rand())-1\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::conName++;
	  blkpos = getBlkPos();
	  string blockzero = "\"Constant"+to_string(Simulink::conName)+"\"";
	  Simulink::addBlock(tempSID,"Constant",blockzero,"0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  Simulink::relationalOptName++;
	  blkpos = getBlkPos();
	  string blockrelation = "\"Relational\\nOperator"+to_string(Simulink::relationalOptName)+"\"";
	  Simulink::addBlock(tempSID,"RelationalOperator",blockrelation,"",2,"\"<\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::addLine(tempSID,key,1,blockrelation,1);
	  Simulink::addLine(tempSID,blockzero,1,blockrelation,2);

	  string blockRandom = blockrelation;

	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd1,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd2,"",3,"\"AND\"","3",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2+10);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd3 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd3,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockNot1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockNot1,"",1,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockOr1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockOr1,"",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockOr2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockOr2,"",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string blockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",blockDelay1,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::addLine(tempSID,blockReady,portReady,blockAnd1,1);
	  Simulink::addLine(tempSID,blockRandom,1,blockAnd1,2);
	  Simulink::addLine(tempSID,blockAnd1,1,blockOr1,1);
	  Simulink::addLine(tempSID,blockReady,portReady,blockNot1,1);
	  Simulink::addLine(tempSID,blockNot1,1,blockOr1,2);
	  Simulink::addLine(tempSID,blockOr1,1,blockAnd2,3);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd2,1);
	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++)
	  {
	    string s = getBlockInfoInport(p->op.node[1],k);
	    if(s.find("ready") < s.length())
	    {
	      Simulink::addLine(tempSID,s,1,blockAnd2,2);
	      break;
	    }
	  }
	  Simulink::addLine(tempSID,blockAnd2,1,blockOr2,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,blockAnd3,1);
	  Simulink::addLine(tempSID,blockAnd3,1,blockOr2,2);
	  Simulink::addLine(tempSID,blockOr2,1,blockDelay1,1);
	  Simulink::addLine(tempSID,blockDelay1,1,blockAnd3,2);
  	  Simulink::addLine(tempSID,blockOr2,1,getBlockInfoName(p->op.node[1]),getBlockInfoInport(p->op.node[1],"\"In_ok\""));

	  string blockOk1 = blockOr2;

	  // blkpos = getBlkPos(); //Compute ok for P
	  // Simulink::logicalOptName++;
	  // string blockNot2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  // Simulink::addBlock(tempSID,"Logic",blockNot2,"",1,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  // Simulink::addLine(tempSID,blockOk1,1,blockNot2,1);
	  // Simulink::addLine(tempSID,blockNot2,1,getBlockInfoName(p->op.node[0]),getBlockInfoInport(p->op.node[0],"\"In_ok\""));

	  blkpos = getBlkPos(); //Compute ok for P
	  Simulink::logicalOptName++;
	  string pblockNot0 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",pblockNot0,"",1,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::addLine(tempSID,blockRandom,1,pblockNot0,1);

	  string pblockRandom = pblockNot0;

	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string pblockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",pblockAnd1,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string pblockAnd2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",pblockAnd2,"",3,"\"AND\"","3",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2+10);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string pblockAnd3 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",pblockAnd3,"",2,"\"AND\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string pblockNot1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",pblockNot1,"",1,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string pblockOr1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",pblockOr1,"",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string pblockOr2 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",pblockOr2,"",2,"\"OR\"","2",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  blkpos = getBlkPos();
	  Simulink::delayName++;
	  string pblockDelay1 = "\"Unit Delay"+to_string(Simulink::delayName)+"\"";
	  Simulink::addBlock(tempSID,"UnitDelay",pblockDelay1,"\"0\"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	  Simulink::addLine(tempSID,pblockReady,pportReady,pblockAnd1,1);
	  Simulink::addLine(tempSID,pblockRandom,1,pblockAnd1,2);
	  Simulink::addLine(tempSID,pblockAnd1,1,pblockOr1,1);
	  Simulink::addLine(tempSID,pblockReady,pportReady,pblockNot1,1);
	  Simulink::addLine(tempSID,pblockNot1,1,pblockOr1,2);
	  Simulink::addLine(tempSID,pblockOr1,1,pblockAnd2,3);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,pblockAnd2,1);
	  Simulink::addLine(tempSID,blockReady,portReady,pblockAnd2,2);
	  Simulink::addLine(tempSID,pblockAnd2,1,pblockOr2,1);
	  Simulink::addLine(tempSID,"\"In_ok\"",1,pblockAnd3,1);
	  Simulink::addLine(tempSID,pblockAnd3,1,pblockOr2,2);
	  Simulink::addLine(tempSID,pblockOr2,1,pblockDelay1,1);
	  Simulink::addLine(tempSID,pblockDelay1,1,pblockAnd3,2);
  	  Simulink::addLine(tempSID,pblockOr2,1,getBlockInfoName(p->op.node[0]),getBlockInfoInport(p->op.node[0],"\"In_ok\""));

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Inports of P
	  {
	    string s = getBlockInfoInport(p->op.node[0],k);
	    if(s == "\"In_ok\"")
	      continue;
	    Simulink::inName++;
	    blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	    addBlockInfoInport(p,Simulink::inName,s);
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	    Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[0]),k);
	  }
	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Inports of Q
	  {
	    string s = getBlockInfoInport(p->op.node[1],k);
	    if(s == "\"In_ok\"")
	      continue;
	    if(getBlockInfoInport(p->op.node[0],s) == -1)
	    {
	      Simulink::inName++;
	      blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Inport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      addBlockInfoInport(p,Simulink::inName,s);
	      Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	    }
	    Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Outports of P
	  {
	    string s = getBlockInfoOutport(p->op.node[0],k);
	    if(s == "\"Out_ok\"" || s == "\"Out_Ready\"")
	      continue;
	    else if(s.find("ready") < s.length() || s.find("ch")<s.length() || getBlockInfoOutport(p->op.node[1],s) == -1)
	    {
	      Simulink::outName++;
	      blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,s,1);
	    }
	    else
	    {
	      Simulink::outName++;
	      blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);

	      Simulink::switchName++; //switch outputs by ok of Q
	      blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Switch","\"Switch"+to_string(Simulink::switchName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+20,blkpos.y2+10);
	      
	      Simulink::addLine(tempSID,blockOk1,1,"\"Switch"+to_string(Simulink::switchName)+"\"",2);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],s),"\"Switch"+to_string(Simulink::switchName)+"\"",1);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],s),"\"Switch"+to_string(Simulink::switchName)+"\"",3);
	      Simulink::addLine(tempSID,"\"Switch"+to_string(Simulink::switchName)+"\"",1,s,1);
	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Outports of Q
	  {
	    string s = getBlockInfoOutport(p->op.node[1],k);
	    if(s == "\"Out_ok\"" || s == "\"Out_Ready\"")
	      continue;
	    else if(s.find("ready") < s.length() || s.find("ch")<s.length() || getBlockInfoOutport(p->op.node[0],s) == -1)
	    {
	      Simulink::outName++;
	      blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,s,1);
	    }
	  }

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;
        case 21:      //Parallel "CON"
	{
	  DstBlock = "";

	  blkpos = getBlkPos();
	  Simulink::subSysName++;
	  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
	  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);
	  setBlockInfoName(p,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
	  tempSID = Simulink::subSysName;

	  toSimulink1(p->op.node[0]);
	  toSimulink1(p->op.node[1]);

	  Simulink::inName = 0;
	  Simulink::outName = 0;

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Inports of P
	  {
	    string s = getBlockInfoInport(p->op.node[0],k);
	    if(s.find("ready") < s.length() || s.find("ch")<s.length() || s == "\"In_ok\"")
	      continue;

	    if(getBlockInfoInport(p->op.node[1],s) != -1) //Detect of shared variables
	    {
	      cout<<"shared variable "<<s[4]<<" detected."<<endl;
	      continue;
	    }

	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",s,"",0,"","",145, 285+65*(k-1), 175, 305+65*(k-1));
	    addBlockInfoInport(p,Simulink::inName,s);
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	    Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[0]),k);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Inports of Q
	  {
	    string s = getBlockInfoInport(p->op.node[1],k);
	    if(s.find("ready") < s.length() || s.find("ch")<s.length() || s == "\"In_ok\"")
	      continue;

	    Simulink::inName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Inport",s,"",0,"","",660, 155+65*(k-1), 690, 175+65*(k-1));
	    addBlockInfoInport(p,Simulink::inName,s);
	    Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,s);
	    Simulink::addLine(tempSID,s,1,getBlockInfoName(p->op.node[1]),k);
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Outports of P
	  {
	    string s = getBlockInfoOutport(p->op.node[0],k);
	    if(s.find("ready") < s.length() || s.find("ch")<s.length() || s == "\"Out_ok\"")
	      continue;

	    Simulink::outName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",s,"",0,"","",485, 465+65*(k-1), 515, 485+65*(k-1));
	    addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	    Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,s,1);
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Outports of Q
	  {
	    string s = getBlockInfoOutport(p->op.node[1],k);
	    if(s.find("ready") < s.length() || s.find("ch")<s.length() || s == "\"Out_ok\"")
	      continue;

	    Simulink::outName++;
	    // blkpos = getBlkPos();
	    Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1140, 335+65*(k-1), 1170, 355+65*(k-1));
	    addBlockInfoOutport(p,Simulink::outName,s);
	    Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	    Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,s,1);
	  }

	  for(k=1;getBlockInfoInport(p->op.node[1],k)!="";k++) //Draw lines from P to Q
	  {
	    int count = 0;
	    int m,n;
	    string r;
	    string s = getBlockInfoInport(p->op.node[1],k);
	    if(s.find("ready") < s.length())
	    {
	      n = 0;
	      s = s.replace(1,2,"Out");
	      s.erase(s.end()-1); //erase the last " in s to find s in r
	      s = s+"_";
	      for(m=1;getBlockInfoOutport(p->op.node[0],m)!="";m++)
	      {
		r = getBlockInfoOutport(p->op.node[0],m);
		if(r.find(s) < r.length())
		  n++;
	      }
	      if(n > 0)
	      {
		if(n == 1)
		{
		  for(m=1;getBlockInfoOutport(p->op.node[0],m)!="";m++)
		  {
		    r = getBlockInfoOutport(p->op.node[0],m);
		    if(r.find(s) < r.length())
		    {
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,getBlockInfoName(p->op.node[1]),k);
		      break;
		    }
		  }
		}
		else
		{
		  // blkpos = getBlkPos();
		  Simulink::logicalOptName++;
		  string blockOr = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
		  Simulink::addBlock(tempSID,"Logic",blockOr,"",n,"\"OR\"",to_string(n),565, 507, 595, 528+(n-1)*10);
		  Simulink::addLine(tempSID,blockOr,1,getBlockInfoName(p->op.node[1]),k);
		  n = 1;
		  for(m=1;getBlockInfoOutport(p->op.node[0],m)!="";m++)
		  {
		    r = getBlockInfoOutport(p->op.node[0],m);
		    if(r.find(s) < r.length())
	            {
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,blockOr,n);
		      n++;
		    }
		  }
		}
	      }
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[1],k),"",0,"","",660, 335+65*(k-1), 690, 355+65*(k-1));
		addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[1],k));
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[1],k));
		Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[1],k),1,getBlockInfoName(p->op.node[1]),k);
	      }
	    }
	    else if(s.find("ch")<s.length())
	    {
	      n = 0;
	      s = s.replace(1,2,"Out");
	      s.erase(s.end()-1); //erase the last " in s to find s in r
	      s = s+"_";
	      for(m=1;getBlockInfoOutport(p->op.node[0],m)!="";m++)
	      {
		r = getBlockInfoOutport(p->op.node[0],m);
		if(r.find(s) < r.length())
		  n++;
	      }
	      if(n > 0)
	      {
		if(n == 1)
		{
		  for(m=1;getBlockInfoOutport(p->op.node[0],m)!="";m++)
	          {
		    r = getBlockInfoOutport(p->op.node[0],m);
		    if(r.find(s) < r.length())
		    {
		      // blkpos = getBlkPos();
		      Simulink::productName++;
		      string blockpro = "\"Divide"+to_string(Simulink::productName)+"\"";
		      Simulink::addBlock(tempSID,"Product",blockpro,"",2,"","**",565, 360, 595, 370+(n-1)*10);
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,blockpro,2);
		      string w = r.replace(5,0,"ready_");
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],w),blockpro,1);
		      r = r.replace(5,6,"");
		      Simulink::addLine(tempSID,blockpro,1,getBlockInfoName(p->op.node[1]),k);
		      break;
		    }
		  }
		}
		else
		{
		  // blkpos = getBlkPos();
		  Simulink::sumName++;
		  string blocksum = "\"Add"+to_string(Simulink::sumName)+"\"";
		  Simulink::addBlock(tempSID,"Sum",blocksum,"",n,"",to_string(n),705, 412, 735, 433+(n-1)*10);
		  Simulink::addLine(tempSID,blocksum,1,getBlockInfoName(p->op.node[1]),k);
		  n = 1;
		  for(m=1;getBlockInfoOutport(p->op.node[0],m)!="";m++)
	          {
		    r = getBlockInfoOutport(p->op.node[0],m);
		    if(r.find(s) < r.length())
		    {
		      // blkpos = getBlkPos();
		      Simulink::productName++;
		      string blockpro = "\"Divide"+to_string(Simulink::productName)+"\"";
		      Simulink::addBlock(tempSID,"Product",blockpro,"",2,"","**",565, 360+65*count, 595, 370+(n-1)*10+65*count);
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),m,blockpro,2);
		      string w = r.replace(5,0,"ready_");
		      // cout<<"w:"<<w<<endl;
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],w),blockpro,1);
		      r = r.replace(5,6,"");
		      // cout<<"r: "<<r<<endl;
		      Simulink::addLine(tempSID,blockpro,1,blocksum,n);
		      n++;
		      count++;
		    }
		  }
		}
	      }
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[1],k),"",0,"","",660, 345+65*(k-1), 690, 365+65*(k-1));
		addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[1],k));
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[1],k));
		Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[1],k),1,getBlockInfoName(p->op.node[1]),k);
	      }
	    }
	  }

	  // for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Draw lines from Q to P
	  // {
	  //   int m,n;
	  //   string r;
	  //   string s = getBlockInfoInport(p->op.node[0],k);
	  //   if(s.find("ready") < s.length())
	  //   {
	  //     n = 0;
	  //     s = s.replace(1,2,"Out");
	  //     s.erase(s.end()-1); //erase the last " in s to find s in r
	  //     s = s+"_";
	  //     for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	  //     {
	  // 	r = getBlockInfoOutport(p->op.node[1],m);
	  // 	if(r.find(s) < r.length())
	  // 	  n++;
	  //     }
	  //     blkpos = getBlkPos();
	  //     Simulink::logicalOptName++;
	  //     string blockOr = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  //     Simulink::addBlock(tempSID,"Logic",blockOr,"",n,"\"OR\"",to_string(n),blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2+(n-1)*10);
	  //     Simulink::addLine(tempSID,blockOr,1,getBlockInfoName(p->op.node[0]),k);
	  //     n = 1;
	  //     for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	  //     {
	  // 	r = getBlockInfoOutport(p->op.node[1],m);
	  // 	if(r.find(s) < r.length())
	  // 	{
	  // 	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),m,blockOr,n);
	  // 	  n++;
	  // 	}
	  //     }
	  //   }
	  //   else if(s.find("ch")<s.length())
	  //   {
	  //     n = 0;
	  //     s = s.replace(1,2,"Out");
	  //     s.erase(s.end()-1); //erase the last " in s to find s in r
	  //     s = s+"_";
	  //     for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	  //     {
	  // 	r = getBlockInfoOutport(p->op.node[1],m);
	  // 	if(r.find(s) < r.length())
	  // 	  n++;
	  //     }
	  //     blkpos = getBlkPos();
	  //     Simulink::sumName++;
	  //     string blocksum = "\"Add"+to_string(Simulink::sumName)+"\"";
	  //     Simulink::addBlock(tempSID,"Sum",blocksum,"",n,"",to_string(n),blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2+(n-1)*10);
	  //     Simulink::addLine(tempSID,blocksum,1,getBlockInfoName(p->op.node[0]),k);
	  //     n = 1;
	  //     for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	  //     {
	  // 	r = getBlockInfoOutport(p->op.node[1],m);
	  // 	if(r.find(s) < r.length())
	  // 	{
	  // 	  blkpos = getBlkPos();
	  // 	  Simulink::productName++;
	  // 	  string blockpro = "\"Divide"+to_string(Simulink::productName)+"\"";
	  // 	  Simulink::addBlock(tempSID,"Product",blockpro,"",2,"","**",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2+(n-1)*10);
	  // 	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),m,blockpro,2);
	  // 	  string w = r.replace(5,0,"ready_");
	  // 	  // cout<<"w:"<<w<<endl;
	  // 	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],w),blockpro,1);
	  // 	  r = r.replace(5,6,"");
	  // 	  // cout<<"r: "<<r<<endl;
	  // 	  Simulink::addLine(tempSID,blockpro,1,blocksum,n);
	  // 	  n++;
	  // 	}
	  //     }
	  //   }
	  // }

	  for(k=1;getBlockInfoInport(p->op.node[0],k)!="";k++) //Draw lines from Q to P
	  {
	    int count = 0;
	    int m,n;
	    string r;
	    string s = getBlockInfoInport(p->op.node[0],k);
	    if(s.find("ready") < s.length())
	    {
	      n = 0;
	      s = s.replace(1,2,"Out");
	      s.erase(s.end()-1); //erase the last " in s to find s in r
	      s = s+"_";
	      for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	      {
		r = getBlockInfoOutport(p->op.node[1],m);
		if(r.find(s) < r.length())
		  n++;
	      }
	      if(n > 0)
	      {
		if(n == 1)
		{
		  for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
		  {
		    r = getBlockInfoOutport(p->op.node[1],m);
		    if(r.find(s) < r.length())
		    {
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),m,getBlockInfoName(p->op.node[0]),k);
		      break;
		    }
		  }
		}
		else
		{
		  // blkpos = getBlkPos();
		  Simulink::logicalOptName++;
		  string blockOr = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
		  Simulink::addBlock(tempSID,"Logic",blockOr,"",n,"\"OR\"",to_string(n),755, 517, 785, 548+(n-1)*10);
		  Simulink::addLine(tempSID,blockOr,1,getBlockInfoName(p->op.node[0]),k);
		  n = 1;
		  for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
		  {
		    r = getBlockInfoOutport(p->op.node[1],m);
		    if(r.find(s) < r.length())
	            {
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),m,blockOr,n);
		      n++;
		    }
		  }
		}
	      }
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[0],k),"",0,"","",145, 410+65*(k-1), 175, 430+65*(k-1));
		addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[0],k));
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[0],k));
		Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[0],k),1,getBlockInfoName(p->op.node[0]),k);
	      }
	    }
	    else if(s.find("ch")<s.length())
	    {
	      n = 0;
	      s = s.replace(1,2,"Out");
	      s.erase(s.end()-1); //erase the last " in s to find s in r
	      s = s+"_";
	      for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	      {
		r = getBlockInfoOutport(p->op.node[1],m);
		if(r.find(s) < r.length())
		  n++;
	      }
	      if(n > 0)
	      {
		if(n == 1)
		{
		  for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	          {
		    r = getBlockInfoOutport(p->op.node[1],m);
		    if(r.find(s) < r.length())
		    {
		      // blkpos = getBlkPos();
		      Simulink::productName++;
		      string blockpro = "\"Divide"+to_string(Simulink::productName)+"\"";
		      Simulink::addBlock(tempSID,"Product",blockpro,"",2,"","**",595, 360, 625, 370+(n-1)*10);
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),m,blockpro,2);
		      string w = r.replace(5,0,"ready_");
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],w),blockpro,1);
		      r = r.replace(5,6,"");
		      Simulink::addLine(tempSID,blockpro,1,getBlockInfoName(p->op.node[0]),k);
		      break;
		    }
		  }
		}
		else
		{
		  // blkpos = getBlkPos();
		  Simulink::sumName++;
		  string blocksum = "\"Add"+to_string(Simulink::sumName)+"\"";
		  Simulink::addBlock(tempSID,"Sum",blocksum,"",n,"",to_string(n),735, 412, 765, 433+(n-1)*10);
		  Simulink::addLine(tempSID,blocksum,1,getBlockInfoName(p->op.node[0]),k);
		  n = 1;
		  for(m=1;getBlockInfoOutport(p->op.node[1],m)!="";m++)
	          {
		    r = getBlockInfoOutport(p->op.node[1],m);
		    if(r.find(s) < r.length())
		    {
		      // blkpos = getBlkPos();
		      Simulink::productName++;
		      string blockpro = "\"Divide"+to_string(Simulink::productName)+"\"";
		      Simulink::addBlock(tempSID,"Product",blockpro,"",2,"","**",595, 360+65*count, 625, 370+(n-1)*10+65*count);
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),m,blockpro,2);
		      string w = r.replace(5,0,"ready_");
		      // cout<<"w:"<<w<<endl;
		      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],w),blockpro,1);
		      r = r.replace(5,6,"");
		      // cout<<"r: "<<r<<endl;
		      Simulink::addLine(tempSID,blockpro,1,blocksum,n);
		      n++;
		      count++;
		    }
		  }
		}
	      }
	      else
	      {
		Simulink::inName++;
		// blkpos = getBlkPos();
		Simulink::addBlock(tempSID,"Inport",getBlockInfoInport(p->op.node[0],k),"",0,"","",145, 430+65*(k-1), 175, 450+65*(k-1));
		addBlockInfoInport(p,Simulink::inName,getBlockInfoInport(p->op.node[0],k));
		Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,getBlockInfoInport(p->op.node[0],k));
		Simulink::addLine(tempSID,getBlockInfoInport(p->op.node[0],k),1,getBlockInfoName(p->op.node[0]),k);
	      }
	    }
	  }

	  for(k=1;getBlockInfoOutport(p->op.node[0],k)!="";k++) //Add free outports for P
	  {
	    string s = getBlockInfoOutport(p->op.node[0],k);
	    if((s.find("ready") < s.length() || s.find("ch")<s.length()) && !Simulink::inThisLinelist(tempSID,getBlockInfoName(p->op.node[0]),k))
	    {
	      Simulink::outName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",485, 465+65*(k-1), 515, 485+65*(k-1));
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),k,s,1);
	    }
	  }
	  for(k=1;getBlockInfoOutport(p->op.node[1],k)!="";k++) //Add free outports for Q
	  {
	    string s = getBlockInfoOutport(p->op.node[1],k);
	    if((s.find("ready") < s.length() || s.find("ch")<s.length()) && !Simulink::inThisLinelist(tempSID,getBlockInfoName(p->op.node[1]),k))
	    {
	      Simulink::outName++;
	      // blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",1140, 335+65*(k-1), 1170, 355+65*(k-1));
	      addBlockInfoOutport(p,Simulink::outName,s);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
	      Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),k,s,1);
	    }
	  }

	  Simulink::inName++; //Add ok
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Inport","\"In_ok\"","",0,"","",145, 155, 175, 175);
	  addBlockInfoInport(p,Simulink::inName,"\"In_ok\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,"\"In_ok\"");

	  Simulink::addLine(tempSID,"\"In_ok\"",1,getBlockInfoName(p->op.node[0]),getBlockInfoInport(p->op.node[0],"\"In_ok\""));
	  Simulink::addLine(tempSID,"\"In_ok\"",1,getBlockInfoName(p->op.node[1]),getBlockInfoInport(p->op.node[1],"\"In_ok\""));

	  Simulink::outName++; //Add ok'
	  // blkpos = getBlkPos();
	  Simulink::addBlock(tempSID,"Outport","\"Out_ok\"","",0,"","",1140, 160, 1170, 180);
	  addBlockInfoOutport(p,Simulink::outName,"\"Out_ok\"");
	  Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,"\"Out_ok\"");

	  // blkpos = getBlkPos();
	  Simulink::logicalOptName++;
	  string blockAnd1 = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  Simulink::addBlock(tempSID,"Logic",blockAnd1,"",2,"\"AND\"","2",995, 160, 1025, 180);

	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[0]),getBlockInfoOutport(p->op.node[0],"\"Out_ok\""),blockAnd1,1);
	  Simulink::addLine(tempSID,getBlockInfoName(p->op.node[1]),getBlockInfoOutport(p->op.node[1],"\"Out_ok\""),blockAnd1,2);
	  Simulink::addLine(tempSID,blockAnd1,1,"\"Out_ok\"",1);

	  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
	  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);
	  return;
	}break;

        default: break;
      }
      for(i=0;i<p->op.num;i++)
      {
	if((p->op.node[i])->type == TYPE_CONTENT)
        {
	  Simulink::conName++;
	  SrcBlock = "\"Constant"+to_string(Simulink::conName)+"\"";
	}
	else if(p->op.node[i]->type == TYPE_INDEX)
	{
	  if(i != 0 || (i == 0 && getOpType(p->op.name) != 12))
	  {
	    SrcBlock = "\"In_"+p->op.node[i]->index+"\"";
	    if(!Simulink::inThisBlocklist(tempSID,SrcBlock))
	    {
	      Simulink::inName++;
	      blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Inport",SrcBlock,"0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      addBlockInfoInport(p->op.node[i],Simulink::inName,SrcBlock);
	      Simulink::addSubsystemInport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::inName,SrcBlock);
	    }
	    string tempBlock = SrcBlock.replace(1,2,"Out"); //Add a respective outport for each inport
	    SrcBlock = SrcBlock.replace(1,3,"In");
	    if(!Simulink::inThisBlocklist(tempSID,tempBlock))
	    {
	      Simulink::outName++;
	      blkpos = getBlkPos();
	      Simulink::addBlock(tempSID,"Outport",tempBlock,"0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	      addBlockInfoOutport(p->op.node[i],Simulink::outName,tempBlock);
	      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,tempBlock);
	    }
	    //if(p->op.node[i]->index != p->op.node[0]->index) 
	    Simulink::addLine(tempSID,SrcBlock,1,tempBlock,1); //Directly output the unchanged inport
	  }
	  else
	  {
	    SrcBlock = "";
	  }
	}
	else if((p->op.node[i])->type == TYPE_OP)
	{
	  switch(getOpType((p->op.node[i])->op.name))
	  {
	    case 1:
	    {
	      Simulink::sumName++;
	      SrcBlock = "\"Add"+to_string(Simulink::sumName)+"\"";
	    } break;
	    case 2:
	    {
	      Simulink::productName++;
	      SrcBlock = "\"Divide"+to_string(Simulink::productName)+"\"";
	    } break;
	    default: break;
	  }
	}
	if(SrcBlock != "" && DstBlock != "")
	{
	  // if(DstBlock.find("SubSystem")<DstBlock.length() && tempDstPort!=-1)
	  // {
	    // Simulink::addLine(tempSID,SrcBlock,1,DstBlock,tempDstPort);
	    // tempDstPort = -1;
	  // }
	  // else
	  Simulink::addLine(tempSID,SrcBlock,1,DstBlock,i+1);
	}

	toSimulink1(p->op.node[i]);
      }
    }break;
    default: break;
  }
  return;
}
