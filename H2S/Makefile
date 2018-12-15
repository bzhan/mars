hcsp2sim:

	@echo ""
	@echo "HCSP process:"
	@cat process

	@echo ""
	@echo "Generating parser..."
	@flex hcsp.l
	@bison -d hcsp.y --warnings=none

	@echo ""
	@echo "Compiling source codes..."
	@g++ *.c *.cpp -x c++ -std=c++0x -I $(OGDFHOME) -lOGDF -lpthread -ll -o Parser

	@echo ""
	@echo "Removing intermediate files..."
	@rm -rf *~
	@rm -rf hcsp.t*
	@rm -rf lex.yy.c

	@echo ""
	@echo "Running translator Hcsp2Sim..."
	@./Parser < process

	@#rm Parser
	@#echo ""
	@#echo "Starting a lite version of Simulink..."
	@#$(MATLABHOME)/matlab -nodesktop -nosplash -nojvm -r "uiopen('h2s.mdl',1)"
