
#test for hpicalculus parser
from Hpicalculus import parser
file1 = open("Hpicalculus\case1.txt", "r",encoding='utf-8')
text= file1.read()
file1.close()
info = parser.parse_file(text)

#test for hcsp parser
# from ss2hcsp.hcsp import parser as pa
# file2 = open("Examples\HCSP\dds_best_effort_continuous.txt", "r")
# text = file2.read()
# file2.close()
# info = pa.parse_file(text)

a=1;
