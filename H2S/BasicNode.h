#ifndef BASICNODE_H
#define BASICNODE_H

#include <cstdarg>    //Variadic functions allowed
// #include <stdlib.h>
// #include <time.h>     //Generating random numbers
#include <ogdf/basic/Graph.h>
#include <ogdf/basic/GraphAttributes.h>
#include "Simulink.h"

#define random(x) (rand()%x)

using namespace ogdf;

struct blockPosition
{
  int x1,y1,x2,y2;
};
static queue<blockPosition> bpq;

static Graph G;
static GraphAttributes GA(G,GraphAttributes::nodeGraphics | GraphAttributes::edgeGraphics);

typedef enum {TYPE_CONTENT,TYPE_INDEX,TYPE_OP}NodeEnum;

typedef struct
{
  string name;
  int num;
  struct NodeTag* node[1];
}OpNode;

typedef struct
{
  string blockname;
  map<int,string> inList;
  map<int,string> outList;
}BlockInfo;

typedef struct NodeTag
{
  NodeEnum type;
  OpNode op;
  BlockInfo blkinfo;

  string blockname;  //Weird duplicated declaration to avoid "Core Dump".
  map<int,string> inList;
  map<int,string> outList;

  string indexname;
  string index;
  string content;
}Node;

class BasicNode
{
 public:
  static int seed; //Seed for generating random numbers
  BasicNode(){}
  ~BasicNode(){}

  static string transVar(const string name);
  static Node* new_operator_Node(const string name,int num,...);
  static Node* new_index_Node(const string iname,const string value);
  static Node* new_content_Node(const string value);
  static Node* mod_index_Node(const string iname,Node* p);
  static void freeNode(Node* p);

  static void printLine();
  static void printTree(Node* p);
  static void printTree1(Node* p,int level);

  blockPosition getBlkPos();
  void autoLayout(Node* p);
  void autoLayout1(Node* p,node& nd);

  void setBlockInfoName(Node* p,const string bname);
  void addBlockInfoInport(Node* p,const int index,const string inname);
  void addBlockInfoOutport(Node* p,const int index,const string outname);
  string getBlockInfoName(Node* p);
  int getBlockInfoInport(Node* p,const string inname);
  string getBlockInfoInport(Node* p,const int index); //Function overloading
  int getBlockInfoOutport(Node* p,const string outname);
  string getBlockInfoOutport(Node* p,const int index); //Function overloading

  virtual int getOpType(string name){}
  virtual void shrinkTree(Node* p){}
  virtual void toSimulink(Node* p){}
  /* virtual void toSimulink1(Node* p,Node* root){} */
};

#endif
