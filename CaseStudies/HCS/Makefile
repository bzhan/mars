TARGET_ARCH = linux64
CC     = g++
OPT    = -O2 # -O3
DEBUG  = -g
OTHER  = -Wall -Wno-deprecated
CFLAGS = $(OPT) $(OTHER)
SYSTEMC = /home/yangg/systemc
INCDIR = -I$(SYSTEMC)/include
LIBDIR = -L$(SYSTEMC)/lib-$(TARGET_ARCH)
LIBS = -lsystemc
APP=system
SRCS=system.cpp
all:
	g++ -o $(APP) $(SRCS) $(LIBDIR) $(INCDIR) $(LIBS)
clean:
	rm -rf *.o
