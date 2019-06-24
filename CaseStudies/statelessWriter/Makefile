TARGET_ARCH = linux64
CC     = g++
OPT    = -O2 # -O3
DEBUG  = -g
OTHER  = -Wall -Wno-deprecated
CFLAGS = $(OPT) $(OTHER)
SYSTEMC = /Users/BEAR/systemc-2.3.3
INCDIR = -I$(SYSTEMC)/include
LIBDIR = -L$(SYSTEMC)/lib-$(TARGET_ARCH)
LIBS = -lsystemc
APP=example
SRCS=example.cpp
all:
	g++ -o $(APP) $(SRCS) $(LIBDIR) $(INCDIR) $(LIBS)
clean:
	rm -rf *.o
