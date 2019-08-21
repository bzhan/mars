function RTW_Sid2UrlHash() {
	this.urlHashMap = new Array();
	/* <Root>/In1 */
	this.urlHashMap["isolette:32"] = "isolette.c:160&isolette.h:102";
	/* <Root>/Constant */
	this.urlHashMap["isolette:29"] = "isolette.h:86&isolette_data.c:24";
	/* <Root>/Constant1 */
	this.urlHashMap["isolette:30"] = "isolette.h:85&isolette_data.c:22";
	/* <Root>/Out1 */
	this.urlHashMap["isolette:28"] = "isolette.c:139&isolette.h:107";
	/* <S1>/Constant */
	this.urlHashMap["isolette:5"] = "isolette.c:158";
	/* <S1>/Constant1 */
	this.urlHashMap["isolette:6"] = "isolette.c:159";
	/* <S1>/Gain */
	this.urlHashMap["isolette:11"] = "isolette.c:149&isolette.h:55";
	/* <S1>/Integrator */
	this.urlHashMap["isolette:7"] = "isolette.c:144,150,173,210,279,290&isolette.h:62,68,74,80";
	/* <S1>/Integrator1 */
	this.urlHashMap["isolette:10"] = "isolette.c:134,140,151,170,207,278,288&isolette.h:61,67,73,79";
	/* <S1>/Sum */
	this.urlHashMap["isolette:9"] = "isolette.c:152";
	/* <S1>/Switch */
	this.urlHashMap["isolette:4"] = "isolette.c:157,168&isolette.h:56";
	this.getUrlHash = function(sid) { return this.urlHashMap[sid];}
}
RTW_Sid2UrlHash.instance = new RTW_Sid2UrlHash();
function RTW_rtwnameSIDMap() {
	this.rtwnameHashMap = new Array();
	this.sidHashMap = new Array();
	this.rtwnameHashMap["<Root>"] = {sid: "isolette"};
	this.sidHashMap["isolette"] = {rtwname: "<Root>"};
	this.rtwnameHashMap["<S1>"] = {sid: "isolette:13"};
	this.sidHashMap["isolette:13"] = {rtwname: "<S1>"};
	this.rtwnameHashMap["<Root>/In1"] = {sid: "isolette:32"};
	this.sidHashMap["isolette:32"] = {rtwname: "<Root>/In1"};
	this.rtwnameHashMap["<Root>/Constant"] = {sid: "isolette:29"};
	this.sidHashMap["isolette:29"] = {rtwname: "<Root>/Constant"};
	this.rtwnameHashMap["<Root>/Constant1"] = {sid: "isolette:30"};
	this.sidHashMap["isolette:30"] = {rtwname: "<Root>/Constant1"};
	this.rtwnameHashMap["<Root>/Subsystem"] = {sid: "isolette:13"};
	this.sidHashMap["isolette:13"] = {rtwname: "<Root>/Subsystem"};
	this.rtwnameHashMap["<Root>/Out1"] = {sid: "isolette:28"};
	this.sidHashMap["isolette:28"] = {rtwname: "<Root>/Out1"};
	this.rtwnameHashMap["<S1>/In1"] = {sid: "isolette:14"};
	this.sidHashMap["isolette:14"] = {rtwname: "<S1>/In1"};
	this.rtwnameHashMap["<S1>/In2"] = {sid: "isolette:17"};
	this.sidHashMap["isolette:17"] = {rtwname: "<S1>/In2"};
	this.rtwnameHashMap["<S1>/In3"] = {sid: "isolette:18"};
	this.sidHashMap["isolette:18"] = {rtwname: "<S1>/In3"};
	this.rtwnameHashMap["<S1>/Constant"] = {sid: "isolette:5"};
	this.sidHashMap["isolette:5"] = {rtwname: "<S1>/Constant"};
	this.rtwnameHashMap["<S1>/Constant1"] = {sid: "isolette:6"};
	this.sidHashMap["isolette:6"] = {rtwname: "<S1>/Constant1"};
	this.rtwnameHashMap["<S1>/Gain"] = {sid: "isolette:11"};
	this.sidHashMap["isolette:11"] = {rtwname: "<S1>/Gain"};
	this.rtwnameHashMap["<S1>/Integrator"] = {sid: "isolette:7"};
	this.sidHashMap["isolette:7"] = {rtwname: "<S1>/Integrator"};
	this.rtwnameHashMap["<S1>/Integrator1"] = {sid: "isolette:10"};
	this.sidHashMap["isolette:10"] = {rtwname: "<S1>/Integrator1"};
	this.rtwnameHashMap["<S1>/Sum"] = {sid: "isolette:9"};
	this.sidHashMap["isolette:9"] = {rtwname: "<S1>/Sum"};
	this.rtwnameHashMap["<S1>/Switch"] = {sid: "isolette:4"};
	this.sidHashMap["isolette:4"] = {rtwname: "<S1>/Switch"};
	this.rtwnameHashMap["<S1>/Out1"] = {sid: "isolette:15"};
	this.sidHashMap["isolette:15"] = {rtwname: "<S1>/Out1"};
	this.getSID = function(rtwname) { return this.rtwnameHashMap[rtwname];}
	this.getRtwname = function(sid) { return this.sidHashMap[sid];}
}
RTW_rtwnameSIDMap.instance = new RTW_rtwnameSIDMap();
