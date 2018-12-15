#ifndef BOOLEXPRESSION_H
#define BOOLEXPRESSION_H

#include "BasicNode.h"

class BoolExpression:public BasicNode
{
 private:
  Node* root;

 public:
  BoolExpression(){}
  BoolExpression(Node* p){root = p;}
  ~BoolExpression(){/*freeNode(root);*/}

  Node* getRoot(){return root;}
  
  virtual int getOpType(string name);
  virtual void shrinkTree(Node* p);
  virtual void toSimulink(Node* p,int tempSID);
  virtual void toSimulink1(Node* p,Node* root);
};

#endif
