#include "ArithExpression.h"

int ArithExpression:: getOpType(string name)
{
  if(name[0] == '+' || name[0] == '-')
    return 1;
  else if(name[0] == '*' || name[0] == '/')
    return 2;
  else
    return -1;
}

void ArithExpression::shrinkTree(Node* p)
{
  int i,j,k,t,m,bak;
  string str;
  int flag = 1;
  int leftright;

  if(p->type != TYPE_OP)
    return;
  else
  {
    if(p->op.num == 1)          //Do not add anything before an UMINUS node
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
    if(flag)             //Add a '+' or '*' before the op.name of p when it has no op-child or the op-child`s opType is different from p`s
    {
      str = p->op.name;
      if(str[0] == '+' || str[0] == '-')
	p->op.name.insert(0,"+");
      else if(str[0] == '*' || str[0] == '/')
	p->op.name.insert(0,"*");
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

void ArithExpression::toSimulink(Node* p){}
void ArithExpression::toSimulink1(Node* p){}

// void ArithExpression::toSimulink(Node* p)
// {
//   string tempSrcBlock;

//   // Simulink::subSysName++;
//   // Simulink::addBlock("SubSystem","\"SubSystem"+to_string(Simulink::subSysName)+"\"","",0,"","");

//   if(p->type == TYPE_CONTENT)
//   {
//     Simulink::conName++;
//     tempSrcBlock = "\"Constant"+to_string(Simulink::conName)+"\"";
//   }
//   else if(p->type == TYPE_OP)
//   {
//     switch(getOpType(p->op.name))
//     {
//       case 1:
//         Simulink::sumName++;
// 	tempSrcBlock = "\"Add"+to_string(Simulink::sumName)+"\"";
// 	break;
//       case 2:
// 	Simulink::productName++;
// 	tempSrcBlock = "\"Divide"+to_string(Simulink::productName)+"\"";
// 	break;
//       default :break;
//     }
//   }
//   toSimulink1(p);

//   //Simulink::outName++;
//   //Simulink::addBlock("Outport","\"Out"+to_string(Simulink::outName)+"\"","",0,"","");

//   // Simulink::addBlock("Outport","\"Out1\"","",0,"","");
//   // Simulink::addLine(tempSrcBlock,1,"\"Out1\"",1);

//   return;
// }

// void ArithExpression::toSimulink1(Node* p)  //Depth first search
// {
//   int i;
//   string DstBlock;
//   string SrcBlock;

//   switch(p->type)
//   {
//     case TYPE_CONTENT :
//       Simulink::addBlock("Constant","\"Constant"+to_string(Simulink::conName)+"\"",p->content,0,"","");break;
//     case TYPE_INDEX :
//     {
//     } break;
//     case TYPE_OP :
//     {
//       switch(getOpType(p->op.name))
//       {
//         case 1:         //'+' '-'
// 	{
// 	  DstBlock = "\"Add"+to_string(Simulink::sumName)+"\"";
// 	  Simulink::addBlock("Sum",DstBlock,"",p->op.num,"",p->op.name);
// 	} break;
//         case 2:       //'*' '/'
// 	{
// 	  DstBlock = "\"Divide"+to_string(Simulink::productName)+"\"";
// 	  Simulink::addBlock("Product",DstBlock,"",p->op.num,"",p->op.name);
// 	} break;
//         default: break;
//       }
//       for(i=0;i<p->op.num;i++)
//       {
// 	if((p->op.node[i])->type == TYPE_CONTENT)
//         {
// 	  Simulink::conName++;
// 	  SrcBlock = "\"Constant"+to_string(Simulink::conName)+"\"";
// 	}
// 	else if((p->op.node[i])->type == TYPE_OP)
//         {
// 	  switch(getOpType((p->op.node[i])->op.name))
// 	  {
// 	    case 1:
// 	    {
// 	      Simulink::sumName++;
// 	      SrcBlock = "\"Add"+to_string(Simulink::sumName)+"\"";
// 	    }break;
// 	    case 2:
// 	    {
// 	      Simulink::productName++;
// 	      SrcBlock = "\"Divide"+to_string(Simulink::productName)+"\"";
// 	    }break;
// 	    default :break;
// 	  }
// 	}

// 	Simulink::addLine(SrcBlock,1,DstBlock,i+1);

// 	toSimulink1(p->op.node[i]);
//       }
//     } break;
//     default: break;
//   }
//   return;
// }
