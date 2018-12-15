#ifndef SIMULINK_H
#define SIMULINK_H

#include <iostream>
#include <string>
#include <stack>
#include <queue>
#include <vector>
#include <map>
#include <set>

using namespace std;

struct Block
{
  int sID;
  string blockType;
  string blockName;
  string blockValue;
  int blockPorts;
  string blockOperator;
  string blockInputs;
  int bx1;
  int by1;
  int bx2;
  int by2;
  Block(int sid,string bt,string bn,string bv,int bp,string bo,string bi,int x1,int y1,int x2,int y2) : sID(sid),blockType(bt),blockName(bn),blockValue(bv),blockPorts(bp),blockOperator(bo),blockInputs(bi),bx1(x1),by1(y1),bx2(x2),by2(y2){}
};

struct Line
{
  int sID;
  string srcBlock;
  int srcPort;
  string dstBlock;
  int dstPort;
  Line(int sid,string sb,int sp,string db,int dp) : sID(sid),srcBlock(sb),srcPort(sp),dstBlock(db),dstPort(dp){}
};

struct Subsystem
{
  string name;
  map<int,string> inList;
  map<int,string> outList;
  Subsystem(string sname,int in,string inname,int out,string outname)
  {
    name = sname;
    if(in != -1)
      inList.insert(pair<int,string>(in,inname));
    if(out != -1)
      outList.insert(pair<int,string>(out,outname));
  }
};

class Simulink
{
 private:
  static vector <Block> blocklist;
  static vector <Line> linelist;
  static vector <Subsystem> sublist;

 public:
  static int subSysName;
  static int inName;
  static int outName;
  static int conName;
  static int sumName;
  static int productName;
  static int logicalOptName;
  static int relationalOptName;
  static int intName;
  static int indexName;
  static int delayName;
  static int randomName;
  static int switchName;
  static int scopeName;
 
 public:
  Simulink(){blocklist.clear();linelist.clear();sublist.clear();}
  ~Simulink(){blocklist.clear();linelist.clear();sublist.clear();}

  static void addBlock(int sid,string bt,string bn,string bv,int bp,string bo,string bi,int x1,int y1,int x2,int y2);
  static void insertHeadBlock(int sid,string bt,string bn,string bv,int bp,string bo,string bi,int x1,int y1,int x2,int y2);
  static void printBlocklist();
  static bool inBlocklist(string bn);
  static bool inThisBlocklist(int s,string bn);
  static int inWhichBlocklist(string bn);

  static void addLine(int sid,string sb,int sp,string db,int dp);
  static void insertHeadLine(int sid,string sb,int sp,string db,int dp);
  static void cutLine(int sid,string sb,int sp,string db,int dp);
  static void breakLine(int sid,string bb,int bi,int bo,string db,int dp);
  static void printLinelist();
  static bool inThisLinelist(int sid,string sb,int sp);
  
  static void addSubsystemInport(string sname,int index,string inname);
  static void addSubsystemOutport(string sname,int index,string outname);
  static void getSubsystemInport(string signal,string& sname,int& index);
  static string getSubsystemInport(string sname,int index);
  static string getSubsystemOutport(string sname,int index);
  static void getSubsystemOutport(string signal,string& sname,int& index);

  static void toMdl();
};

#endif




