#ifndef DIFFERENTIALEQUATIONS_H
#define DIFFERENTIALEQUATIONS_H

#include "BasicNode.h"

class DifferentialEquations:public BasicNode
{
 private:
  Node* root;
  set<string> diffList;

 public:
  DifferentialEquations(){}
  DifferentialEquations(Node* p)
  {
    root = p;
    Node* q = p;
    stack<Node*> s;

    while(q!=NULL || !s.empty())
    {
      while(q!=NULL)
      {
	s.push(q);
	if(q->type == TYPE_OP && getOpType(q->op.name) == 10)
	  diffList.insert(q->op.node[0]->index);
	q = q->op.node[0];
      }
      if(!s.empty())
      {
	q = s.top();
	s.pop();
	if(q->op.num > 0)
	  q = q->op.node[1];
	else
	  q = NULL;
      }
    }
  }
  ~DifferentialEquations(){/*freeNode(root);*/}

  Node* getRoot(){return root;}

  virtual int getOpType(string name);
  virtual void toSimulink(Node* p,int tempSID);
  virtual void toSimulink1(Node* p,Node* root);
};

#endif
