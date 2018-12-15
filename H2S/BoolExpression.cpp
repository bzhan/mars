#include "BoolExpression.h"

int BoolExpression:: getOpType(string name)
{
  if(name[0] == '+' || name[0] == '-')
    return 1;
  else if(name[0] == '*' || name[0] == '/')
    return 2;
  else if(name[0] == '&')
    return 3;
  else if(name[0] == '|')
    return 4;
  else if(name == "~")
    return 5;
  else if(name == "=")
    return 6;
  else if(name == "<")
    return 7;
  else if(name == ">")
    return 8;
  else
    return -1;
}

void BoolExpression::shrinkTree(Node* p)
{
  int i,j,k,t,m,bak;
  string str;
  int flag = 1;
  int leftright;

  if(p->type != TYPE_OP)
    return;
  else
  {
    if(p->op.num == 1)          //Do not add anything before an '~' node
      flag =0;
    else
      for(i=0;i<p->op.num;i++)
      {
	if((p->op.node[i])->type == TYPE_OP && getOpType((p->op.node[i])->op.name) == getOpType(p->op.name))
	{
	  flag = 0;
	  break;
	}
      }
    if(flag)             //Add a '&' or '|' before the op.name of p when it has no op-child or the op-child`s opType is different from p`s
    {
      str = p->op.name;
      if(str[0] == '&')
	p->op.name.insert(0,"&");
      else if(str[0] == '|')
	p->op.name.insert(0,"|");
    }

    leftright = -1;
    for(i=0;i<p->op.num;i++)
    {      
      shrinkTree(p->op.node[i]);

      if((p->op.node[i])->type == TYPE_OP && getOpType((p->op.node[i])->op.name) == getOpType(p->op.name) && getOpType(p->op.name) != -1)
      {
	bak = (p->op.node[i])->op.num-1;

	if(leftright == -1)
	  p->op.name = (p->op.node[i])->op.name + p->op.name;  //Refresh op.name
	else if(leftright == 1)
	  p->op.name = p->op.name+(p->op.node[i])->op.name;  //Refresh op.name

	for(j=p->op.num;j>i;j--)           //Other children backoff
	{
	  p->op.node[j+bak] = p->op.node[j];  //RAM overflow may occur
	}

	for(k=i+bak;k>=i;k--)              //Insert. Must loop from the tail
        {
	  p->op.node[k] = (p->op.node[i])->op.node[k-i];
	}
	
	p->op.num = p->op.num + bak;
	i = i + bak;
	
	if(p->op.name.length() > p->op.num)
        {
	  m = p->op.name.length() - p->op.num;
	  while(m>0)
          {
	    p->op.name = p->op.name.erase(0,1);
	    m--;
	  }
	}
      }
      leftright = - leftright;
    }
  }
}

void BoolExpression::toSimulink(Node* p,int tempSID)
{
  Node* root = p;
  string tempSrcBlock;
  blockPosition blkpos;
  // int tempSID = Simulink::subSysName;

  Simulink::inName = 0;
  Simulink::outName = 0;

  blkpos = getBlkPos();
  Simulink::subSysName++;
  // Simulink::insertHeadBlock(Simulink::subSysName,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",0,0,0,0);
  Simulink::addBlock(tempSID,"SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2+140,blkpos.y2+64);
  Simulink::addLine(tempSID,"----------"+to_string(Simulink::subSysName),-1,"-----------",-1);

  setBlockInfoName(root,"\"SubSystem"+to_string(Simulink::subSysName)+"\"");
  
  if(p->type == TYPE_CONTENT)
  {
    Simulink::conName++;
    tempSrcBlock = "\"Constant"+to_string(Simulink::conName)+"\"";
  }
  else if(p->type == TYPE_INDEX)
  {
    //Simulink::indexName++;
    //tempSrcBlock = "\"Index_"+p->index+to_string(Simulink::indexName)+"\"";
    tempSrcBlock = "\"In_"+p->index+"\"";
  }
  else if(p->type == TYPE_OP)
  {
    switch(getOpType(p->op.name))
    {
      case 3:
      case 4:
      case 5:
        Simulink::logicalOptName++;
	tempSrcBlock = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	break;
      case 6:
      case 7:
      case 8:
	Simulink::relationalOptName++;
	tempSrcBlock = "\"Relational\\nOperator"+to_string(Simulink::relationalOptName)+"\"";
	break;
      default :break;
    }
  }
  
  toSimulink1(p,root);
  
  Simulink::outName++;
  blkpos = getBlkPos();
  Simulink::addBlock(Simulink::subSysName,"Outport","\"Out"+to_string(Simulink::outName)+"\"","",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

  addBlockInfoOutport(root,Simulink::outName,"\"Out"+to_string(Simulink::outName)+"\"");
  Simulink::addSubsystemOutport("\"SubSystem"+to_string(Simulink::subSysName)+"\"",Simulink::outName,"\"Out"+to_string(Simulink::outName)+"\"");

  Simulink::addLine(Simulink::subSysName,tempSrcBlock,1,"\"Out1\"",1);

  Simulink::addBlock(Simulink::subSysName,"EndSubSystem","\"EndSubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","",0,0,0,0);
  Simulink::addLine(Simulink::subSysName,"~~~~~~~~~~"+to_string(Simulink::subSysName),-1,"~~~~~~~~~~~",-1);

  return;
}

void BoolExpression::toSimulink1(Node* p,Node* root)  //Depth first search
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
      if(p->content == "True")
      {
	Simulink::addBlock(Simulink::subSysName,"Constant","\"True"+to_string(Simulink::conName)+"\"","1",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	Simulink::addBlock(Simulink::subSysName,"DataTypeConversion","\"Constant"+to_string(Simulink::conName)+"\"","",0,"\"boolean\"","",blkpos.x1+50,blkpos.y1,blkpos.x2+80,blkpos.y2);
	Simulink::addLine(Simulink::subSysName,"\"True"+to_string(Simulink::conName)+"\"",1,"\"Constant"+to_string(Simulink::conName)+"\"",1);
      }
      else if(p->content == "False")
      {
	Simulink::addBlock(Simulink::subSysName,"Constant","\"False"+to_string(Simulink::conName)+"\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	Simulink::addBlock(Simulink::subSysName,"DataTypeConversion","\"Constant"+to_string(Simulink::conName)+"\"","",0,"\"boolean\"","",blkpos.x1+50,blkpos.y1,blkpos.x2+80,blkpos.y2);
	Simulink::addLine(Simulink::subSysName,"\"False"+to_string(Simulink::conName)+"\"",1,"\"Constant"+to_string(Simulink::conName)+"\"",1);
      }
      else
	Simulink::addBlock(Simulink::subSysName,"Constant","\"Constant"+to_string(Simulink::conName)+"\"",p->content,0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
    } break;
    case TYPE_INDEX :
    {
      if(!Simulink::inThisBlocklist(Simulink::subSysName,"\"In_"+p->index+"\""))
      {
	blkpos = getBlkPos();
	//Simulink::addBlock(Simulink::subSysName,"Constant","\"Index_"+p->index+to_string(Simulink::indexName)+"\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	Simulink::addBlock(Simulink::subSysName,"Inport","\"In_"+p->index+"\"","0",0,"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);

	Simulink::inName++;
	addBlockInfoInport(root,Simulink::inName,"\"In_"+p->index+"\"");
	Simulink::addSubsystemInport("\"SubSystem"+to_string(Simulink::subSysName)+"\"",Simulink::inName,"\"In_"+p->index+"\"");
      }
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
        case 3:       //'&'
        case 4:       //'|'
        case 5:       //'~'
	{
	  DstBlock = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	  if(getOpType(p->op.name) == 3)
	  {
	    blkpos = getBlkPos();
	    Simulink::addBlock(Simulink::subSysName,"Logic",DstBlock,"",p->op.num,"\"AND\"",to_string(p->op.num),blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  }
	  else if(getOpType(p->op.name) == 4)
	  {
	    blkpos = getBlkPos();
	    Simulink::addBlock(Simulink::subSysName,"Logic",DstBlock,"",p->op.num,"\"OR\"",to_string(p->op.num),blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  }
	  else if(getOpType(p->op.name) == 5)
	  {
	    blkpos = getBlkPos();
	    Simulink::addBlock(Simulink::subSysName,"Logic",DstBlock,"",p->op.num,"\"NOT\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  }
	} break;
        case 6:       //'='
        case 7:       //'<'
        case 8:       //'>'
	{
	  DstBlock = "\"Relational\\nOperator"+to_string(Simulink::relationalOptName)+"\"";
	  if(getOpType(p->op.name) == 6)
	  {
	    blkpos = getBlkPos();
	    Simulink::addBlock(Simulink::subSysName,"RelationalOperator",DstBlock,"",p->op.num,"\"==\"","",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  }
	  else
	  {
	    blkpos = getBlkPos();
	    Simulink::addBlock(Simulink::subSysName,"RelationalOperator",DstBlock,"",p->op.num,p->op.name,"",blkpos.x1,blkpos.y1,blkpos.x2,blkpos.y2);
	  }
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
	  //Simulink::indexName++;
	  //SrcBlock = "\"Index_"+p->op.node[i]->index+to_string(Simulink::indexName)+"\"";
	  SrcBlock = "\"In_"+p->op.node[i]->index+"\"";
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
	    case 3:
	    case 4:
	    case 5:
	    {
	      Simulink::logicalOptName++;
	      SrcBlock = "\"Logical\\nOperator"+to_string(Simulink::logicalOptName)+"\"";
	    } break;
	    case 6:
	    case 7:
	    case 8:
	    {
	      Simulink::relationalOptName++;
	      SrcBlock = "\"Relational\\nOperator"+to_string(Simulink::relationalOptName)+"\"";
	    } break;
	    default :break;
	  }
	}

	if(SrcBlock != "" && DstBlock != "")
	  Simulink::addLine(Simulink::subSysName,SrcBlock,1,DstBlock,i+1);

	toSimulink1(p->op.node[i],root);
      }
    } break;
    default: break;
  }
  return;
}
