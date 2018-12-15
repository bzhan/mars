#include "BasicNode.h"
#include <ogdf/energybased/FMMMLayout.h>  //Energy-based layout 

int BasicNode::seed = 1;

string BasicNode::transVar(const string name)
{
  string tname = name;
  while(tname.find_first_of("_") != string::npos)
    tname.erase(tname.find_first_of("_"),1);
  return tname;
}

Node* BasicNode::new_operator_Node(const string name,int num,...)
{
  va_list valist;
  Node* p;

  int i;

  if((p = new Node) == NULL)
    cout<<"Out of memory"<<endl;

  p->type = TYPE_OP;
  p->op.name = name;
  p->op.num = num;

  va_start(valist,num);

  for(i=0;i<num;i++)
    p->op.node[i] = va_arg(valist,Node*);

  va_end(valist);

  return p;
}

Node* BasicNode::new_index_Node(const string iname,const string value)
{
  Node* p;

  if((p = new Node) == NULL)
    cout<<"Out of memory"<<endl;

  p->type = TYPE_INDEX;
  p->index = value;
  p->indexname = iname;

  return p;
}

Node* BasicNode::new_content_Node(const string value)
{
  Node* p;

  if((p = new Node) == NULL)
    cout<<"Out of memory"<<endl;

  p->type = TYPE_CONTENT;
  p->content = value;

  return p;
} 

Node* BasicNode::mod_index_Node(const string iname,Node* p)
{
  p->indexname = iname;
  return p;
}

void BasicNode::freeNode(Node* p)
{
  int i;
  
  if(!p)
    return;
  
  if(p->type == TYPE_OP)
  {
    for(i=0;i<p->op.num;i++)
      freeNode(p->op.node[i]);
  }
  delete p;
}

void BasicNode::setBlockInfoName(Node* p,const string bname)
{
  p->blockname = bname;
  return;
}

void BasicNode::addBlockInfoInport(Node* p,const int index,const string inname)
{
  p->inList.insert(pair<int,string>(index,inname));
  return;
}

void BasicNode::addBlockInfoOutport(Node* p,const int index,const string outname)
{
  p->outList.insert(pair<int,string>(index,outname));
  return;
}

string BasicNode::getBlockInfoName(Node* p)
{
  return p->blockname;
}

int BasicNode::getBlockInfoInport(Node* p,const string inname)
{
  map<int,string>::iterator it;
  for(it=p->inList.begin();it!=p->inList.end();it++)
  {
    if(it->second == inname)
      return it->first;
  }
  return -1;
}

string BasicNode::getBlockInfoInport(Node* p,const int index)
{
  map<int,string>::iterator it;
  for(it=p->inList.begin();it!=p->inList.end();it++)
  {
    if(it->first == index)
      return it->second;
  }
  return "";
}

int BasicNode::getBlockInfoOutport(Node* p,const string outname)
{
  map<int,string>::iterator it;
  for(it=p->outList.begin();it!=p->outList.end();it++)
  {
    if(it->second == outname)
      return it->first;
  }
  return -1;
}

string BasicNode::getBlockInfoOutport(Node* p,const int index)
{
  map<int,string>::iterator it;
  for(it=p->outList.begin();it!=p->outList.end();it++)
  {
    if(it->first == index)
      return it->second;
  }
  return "";
}

void BasicNode::printLine()
{
  cout<<"-------------------------------------------------------"<<endl;
}

void BasicNode::printTree(Node* p)
{
  printTree1(p,0);
}

void BasicNode::printTree1(Node* p,int level)
{
  int i;
  int j;
  
  if(p->type != TYPE_OP)
  {
    switch(p->type)
    {
      case TYPE_INDEX :
      {
    if(p->indexname == "")
	  cout<<p->index;
	else
	  cout<<p->indexname<<" "<<p->index;
	break;
      }
      case TYPE_CONTENT :
        cout<<p->content;break;
      default: break;
    }

    cout<<endl;
    
    return;
  }
  else
  {
    level++;
    cout<<p->op.name;
    for(i=0;i<p->op.num;i++)
    {
      if(i==0)
	cout<<"\t";
      else
	for(j=0;j<level;j++)
	    cout<<"\t";	
      printTree1(p->op.node[i],level);
    }
  }
}

blockPosition BasicNode::getBlkPos()
{
  blockPosition tempBlkPos;
  if(!bpq.empty())
  {
    tempBlkPos = bpq.front();
    bpq.pop();
  }
  else
  {
    // srand((int) time(0));
    srand(seed);
    tempBlkPos.x1 = random(1400);
    tempBlkPos.x2 = tempBlkPos.x1 + 30;
    seed+=10;
    tempBlkPos.y1 = random(800);
    tempBlkPos.y2 = tempBlkPos.y1 + 20;
    seed+=10;
  }
  return tempBlkPos;
}

void BasicNode::autoLayout(Node* p)    //Energy-based Layout
{
  node v;
  edge e;
  blockPosition blkpos;

  G.clear();           //Remove all the nodes and edges in G

  node nd = G.newNode();
  if(p->type == TYPE_OP)
  {
    GA.width(nd) = 15.0 * p->op.num;
    GA.height(nd) = 10.0 * p->op.num;
  }

  autoLayout1(p,nd);

  node outnode = G.newNode();
  GA.width(outnode) = 30;
  GA.height(outnode) = 20;
  G.newEdge(outnode,nd);

  FMMMLayout fmmm;
  fmmm.useHighLevelOptions(true);
  fmmm.unitEdgeLength(50.0); 
  fmmm.newInitialPlacement(true);
  fmmm.qualityVersusSpeed(FMMMLayout::qvsGorgeousAndEfficient);  
  fmmm.call(GA);

  GA.writeGML("layout.gml");

  if( !GA.readGML(G,"layout.gml") ) 
  {
    cerr << "Could not load layout.gml" << endl;
    return;
  }

  while(!bpq.empty())    //Empty the block-position queue
    bpq.pop();

  forall_nodes(v,G)      //Extract the coordinate into queue
  {
    blkpos.x1 = GA.x(v);
    blkpos.x2 = GA.x(v) + GA.width(v);
    blkpos.y1 = GA.y(v);
    blkpos.y2 = GA.y(v) + GA.height(v);
    bpq.push(blkpos);
  }
  return;
}

void BasicNode::autoLayout1(Node* p,node& nd)
{
  int i;

  if(p->type == TYPE_CONTENT || p->type == TYPE_INDEX)
  {
    GA.width(nd) = 30;
    GA.height(nd) = 20;
    return;
  }
  else if(p->type == TYPE_OP)
  {
    GA.width(nd) = 15.0 * p->op.num;
    GA.height(nd) = 10.0 * p->op.num;
    for(i=0;i<p->op.num;i++)
    {
      node nd1 = G.newNode();
      G.newEdge(nd1,nd);
      autoLayout1(p->op.node[i],nd1);
    }
  }
}
