#ifndef ARITHEXPRESSION_H
#define ARITHEXPRESSION_H

#include "BasicNode.h"

class ArithExpression:public BasicNode
{
 private:
  Node* root;

 public:
  ArithExpression(Node* p){root = p;}
  ~ArithExpression(){freeNode(root);}

  Node* getRoot(){return root;}
  
  virtual int getOpType(string name);
  virtual void shrinkTree(Node* p);
  virtual void toSimulink(Node* p);
  virtual void toSimulink1(Node* p);
};

#endif
