#ifndef HCSPPROCESS_H
#define HCSPPROCESS_H

#include "BasicNode.h"
#include "BoolExpression.h"
#include "DifferentialEquations.h"

class HcspProcess:public BasicNode
{
 private:
  Node* root;
  BoolExpression be; //Forward declaration to avoid "Memory Flush".
  DifferentialEquations de;
  // HcspProcess hp;

 public:
  HcspProcess(){}
  HcspProcess(Node* p){root = p;}
  ~HcspProcess(){/*freeNode(root);*/}

  Node* getRoot(){return root;}

  virtual int getOpType(string name);
  virtual void toSimulink(Node* p);
  virtual void toSimulink1(Node* p);

};

#endif
