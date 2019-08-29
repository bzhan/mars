## 文件夹aadlModel和simulinkModel分别包含了各自model的XML文件

## 直接python运行各自文件夹中的py脚本就可以解析各自的XML文件

##最终返回json文件

json文件格式
	{"model_name": MODEL_NAME
	 "Inport": [inport_1, inport2,...]
	 "Outport": [outport_1, output_2,...]
	}