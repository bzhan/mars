#include "DifferentialEquations.h"

int DifferentialEquations:: getOpType(string name)
{
  if(name[0] == '+' || name[0] == '-')
    return 1;
  else if(name[0] == '*' || name[0] == '/')
    return 2;
  else if(name == "DIFF")
    return 9;
  else if(name == "\'=")
    return 10;
  else
    return -1;
}

void DifferentialEquations::toSimulink(Node* p,int tempSID)
{
  Node* root = p;
  string tempSrcBlock = "";
  blockPosition blkpos;
  // int tempSID = Simulink::subSysName;

  Simulink::inName = 0;
  Simulink::outName = 0;

  blkpos = getBlkPos();
  Simulink::subSysName++;
  // Simulink::insertHeadBlock(Simulink::subSysName,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",0,0,0,0);
  // Simulink::addBlock(Simulink::subSysName,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",0,0,0,0);
  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);

  setBlockInfoName(root,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
  tempSID = Simulink::subSysName;

  blkpos = getBlkPos();
  // Simulink::addBlock(tempSID,"EnablePort","\"Enable\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2); //use an inport other than enableport, fixed on Feb 7, 2015
  Simulink::addBlock(tempSID,"Inport","\"In_enable\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
  Simulink::inName++;
  addBlockInfoInport(root,Simulink::inName,"\"In_enable\"");
  Simulink::addSubsystemInport("\"SubSystem"+to_string(Simulink::subSysName)+"\"",Simulink::inName,"\"In_enable\"");

  // if(getOpType(p->op.name) == 10)
  // {
  //   Simulink::intName++;    
  //   tempSrcBlock = "\"Int_"+to_string(Simulink::intName)+"\"";
  //   tempSrcBlock = "\"Int_"+p->op.node[0]->index+"\"";
  // }
  toSimulink1(p,root);

  // Simulink::outName++;
  // Simulink::addBlock(Simulink::subSysName,"Outport","\"Out_"+to_string(Simulink::outName)+"\"","",0,"","",0,0,0,0);
  // addBlockInfoOutport(root,Simulink::outName,"\"Out_"+to_string(Simulink::outName)+"\""); //Test for Conditional "->"

  for(int k=1;getBlockInfoInport(p,k)!="";k++) //Directly output the unchanged inport
  {
    if(getBlockInfoInport(p,k) == "\"In_enable\"")
      continue;
    string s = getBlockInfoInport(p,k);
    s = s.replace(1,2,"Out");
    if(!Simulink::inThisBlocklist(tempSID,s))
    {
      Simulink::outName++;
      blkpos = getBlkPos();
      Simulink::addBlock(tempSID,"Outport",s,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
      addBlockInfoOutport(p,Simulink::outName,s);
      Simulink::addSubsystemOutport("\"SubSystem"+to_string(tempSID)+"\"",Simulink::outName,s);
      Simulink::addLine(tempSID,getBlockInfoInport(p,k),1,s,1);
    }
  }

  Simulink::addBlock(tempSID,"EndSubSystem","\"EndSubSystem"+to_string(tempSID)+"\"","",0,"","",0,0,0,0);
  Simulink::addLine(tempSID,"~~~~~~~~~~"+to_string(tempSID),-1,"~~~~~~~~~~~",-1);

  return;
}

void DifferentialEquations::toSimulink1(Node* p,Node* root)  //Depth first search
{
  int i;
  string DstBlock;
  string SrcBlock;
  blockPosition blkpos;

  switch(p->type)
  {
    case TYPE_CONTENT :
    {
      blkpos = getBlkPos();
      Simulink::addBlock(Simulink::subSysName,"Constant","\"Constant"+to_string(Simulink::conName)+"\"",p->content,0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
    } break;
    case TYPE_INDEX :
    {
      //blkpos = getBlkPos();
      //Simulink::addBlock(Simulink::subSysName,"Constant","\"Index_"+p->index+to_string(Simulink::indexName)+"\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
    } break;
    case TYPE_OP :
    {
      switch(getOpType(p->op.name))
      {
        case 1:       //'+' '-'
	{
	  DstBlock = "\"Add"+to_string(Simulink::sumName)+"\"";
	  blkpos = getBlkPos();
	  Simulink::addBlock(Simulink::subSysName,"Sum",DstBlock,"",p->op.num,"",p->op.name,blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	} break;
        case 2:       //'*' '/'
	{
	  DstBlock = "\"Divide"+to_string(Simulink::productName)+"\"";
	  blkpos = getBlkPos();
	  Simulink::addBlock(Simulink::subSysName,"Product",DstBlock,"",p->op.num,"",p->op.name,blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	} break;
        case 9:       //"DIFF"
	{
	  // DstBlock = "\"Out_"+p->op.node[0]->index+"\"";
	  // blkpos = getBlkPos();
	  // Simulink::addBlock(Simulink::subSysName,"Outport",DstBlock,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	} break;
        case 10:      //"'="
	{
	  // DstBlock = "\"Int_"+to_string(Simulink::intName)+"\"";
	  // DstBlock = "\"Int_"+p->op.node[0]->index+"\""; // switch added to each integrator block, fixed on Feb 7, 2015
	  DstBlock = "\"Switch_"+p->op.node[0]->index+"\"";

	  blkpos = getBlkPos();
	  Simulink::addBlock(Simulink::subSysName,"Integrator","\"Int_"+p->op.node[0]->index+"\"","",2,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2+20);

	  // blkpos = getBlkPos();
	  Simulink::addBlock(Simulink::subSysName,"Inport","\"In_"+p->op.node[0]->index+"\"","0",0,"","",blkpos.x1-100,blkpos.y1-20,blkpos.x2-100,blkpos.y2-20);
	  Simulink::inName++;
	  addBlockInfoInport(root,Simulink::inName,"\"In_"+p->op.node[0]->index+"\"");
	  Simulink::addSubsystemInport("\"SubSystem"+to_string(Simulink::subSysName)+"\"",Simulink::inName,"\"In_"+p->op.node[0]->index+"\"");

	  blkpos = getBlkPos();
	  Simulink::addBlock(Simulink::subSysName,"Switch","\"Switch_"+p->op.node[0]->index+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+20,blkpos.y2+10);
	  Simulink::conName++; // 0 here used to stop integration
	  Simulink::addBlock(Simulink::subSysName,"Constant","\"Constant"+to_string(Simulink::conName)+"\"","0",0,"","",blkpos.x1-100,blkpos.y1+50,blkpos.x2-100,blkpos.y2+50);

	  Simulink::addLine(Simulink::subSysName,"\"In_enable\"",1,"\"Switch_"+p->op.node[0]->index+"\"",2); 
	  Simulink::addLine(Simulink::subSysName,"\"Constant"+to_string(Simulink::conName)+"\"",1,"\"Switch_"+p->op.node[0]->index+"\"",3);
	  Simulink::addLine(Simulink::subSysName,"\"Switch_"+p->op.node[0]->index+"\"",1,"\"Int_"+p->op.node[0]->index+"\"",1);
	  Simulink::addLine(Simulink::subSysName,"\"In_"+p->op.node[0]->index+"\"",1,"\"Int_"+p->op.node[0]->index+"\"",2);  //Assignment to continuous variable.
	} break;
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
	  // Simulink::indexName++;
	  // SrcBlock = "\"Index_"+p->op.node[i]->index+to_string(Simulink::indexName)+"\"";

	  if(i != 0)
	  {
	    // if(Simulink::inThisBlocklist(Simulink::subSysName,"\"Out_"+p->op.node[i]->index+"\""))
	    if(this->diffList.find(p->op.node[i]->index) != this->diffList.end())
	    {
	      SrcBlock = "\"Int_"+p->op.node[i]->index+"\"";
	      // SrcBlock = "\"Switch_"+p->op.node[i]->index+"\"";
	    }
	    else
	    {
	      SrcBlock = "\"In_"+p->op.node[i]->index+"\"";
	      if(!Simulink::inThisBlocklist(Simulink::subSysName,SrcBlock))
	      {
		blkpos = getBlkPos();
		Simulink::addBlock(Simulink::subSysName,"Inport","\"In_"+p->op.node[i]->index+"\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

		Simulink::inName++;
		addBlockInfoInport(root,Simulink::inName,"\"In_"+p->op.node[i]->index+"\"");
		Simulink::addSubsystemInport("\"SubSystem"+to_string(Simulink::subSysName)+"\"",Simulink::inName,"\"In_"+p->op.node[i]->index+"\"");
	      }
	    }
	  }
	  else if(i == 0)
	  {
	    if(getOpType(p->op.name)==10)
	      {
		SrcBlock = "\"Out_"+p->op.node[0]->index+"\"";
		if(!Simulink::inThisBlocklist(Simulink::subSysName,SrcBlock))
		  {
		    blkpos = getBlkPos();
		    Simulink::addBlock(Simulink::subSysName,"Outport",SrcBlock,"",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
		    
		    Simulink::outName++;
		    addBlockInfoOutport(root,Simulink::outName,"\"Out_"+p->op.node[0]->index+"\"");
		    Simulink::addSubsystemOutport("\"SubSystem"+to_string(Simulink::subSysName)+"\"",Simulink::outName,"\"Out_"+p->op.node[0]->index+"\"");
		  }
	      }
	    else
	      {
		SrcBlock = "\"In_"+p->op.node[i]->index+"\"";
		if(!Simulink::inThisBlocklist(Simulink::subSysName,SrcBlock))
		  {
		    blkpos = getBlkPos();
		    Simulink::addBlock(Simulink::subSysName,"Inport","\"In_"+p->op.node[i]->index+"\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

		    Simulink::inName++;
		    addBlockInfoInport(root,Simulink::inName,"\"In_"+p->op.node[i]->index+"\"");
		    Simulink::addSubsystemInport("\"SubSystem"+to_string(Simulink::subSysName)+"\"",Simulink::inName,"\"In_"+p->op.node[i]->index+"\"");
		  }
	      }
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
	    case 9:
	    {
	    } break;
	    case 10:
	    {
	      //Simulink::intName++;
	      //SrcBlock = "\"Int_"+to_string(Simulink::intName)+"\"";
	      SrcBlock = "\"Int_"+p->op.node[0]->index+"\"";
	      // SrcBlock = "\"Switch_"+p->op.node[0]->index+"\"";
	    }break;
	    default :break;
	  }
	}
	if(SrcBlock != "" && DstBlock != "")
	{
	  if(DstBlock.find("Switch") < DstBlock.length())
	  {
	    if(SrcBlock.find("Out") < SrcBlock.length())
	    {
	      Simulink::addLine(Simulink::subSysName,DstBlock.replace(1,6,"Int"),1,SrcBlock,1);
	      DstBlock.replace(1,3,"Switch");
	    }
	    else
	      Simulink::addLine(Simulink::subSysName,SrcBlock,1,DstBlock,1);
	  }
	  else
	  {
	    if(SrcBlock.find("Out") < SrcBlock.length())
	      SrcBlock.replace(1,3,"Int");
	    Simulink::addLine(Simulink::subSysName,SrcBlock,1,DstBlock,i+1);
	  }
	}
	toSimulink1(p->op.node[i],root);
      }
    } break;
    default: break;
  }
  return;
}
