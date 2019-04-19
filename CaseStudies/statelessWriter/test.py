import sys
import getopt

argv = sys.argv[1:]
opts, args = getopt.getopt(argv, "", ["version=", "workspace="])
for opt, arg in opts:
    if opt == "--version":
        print(arg)
    elif opt == "--workspace":
        print(arg)
