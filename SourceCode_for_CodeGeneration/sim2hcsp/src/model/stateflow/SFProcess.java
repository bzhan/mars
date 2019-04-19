package model.stateflow;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

import m2h.Isabelle;
import m2h.SL2HCSP;

public class SFProcess {
    public static int sfNum = 0;
    public static ArrayList<String> sfName = new ArrayList<String>();
    private static int num = 1;

    protected static ArrayList<String> getMainProcess(Stateflow sf) {
        // choose to print
        if (SL2HCSP.printSFText)
            printTProcess(sf);
        // store processes for each AND sub-diagram
        ArrayList<String> results = new ArrayList<String>();
        if (sf.getDiagram().getCompositeType() == null) {
            System.out.println("A wired stateflow diagram " + sf.getName());
        } else if (sf.getDiagram().getCompositeType().equals("OR")) {
            // shared variables
            String vout = "";
            String vin = "";
            for (String var : sf.getDiagram().getIvars()) {
                vout += "VO1??" + var + 1 + ";";
                vin += ";" + "VI1!!" + var + 1;
            }
            for (String var : sf.getDiagram().getOvars()) {
                vout += "VO1??" + var + 1 + ";";
                vin += ";" + "VI1!!" + var + 1;
            }
            for (String var : sf.getDiagram().getLvars()) {
                vout += "VO1??" + var + 1 + ";";
                vin += ";" + "VI1!!" + var + 1;
            }
            String lprocess = sf.getDiagram().getInit(sf.getLocations());
            lprocess += sf.getDiagram().getEntryProcess(sf.getLocations());
            lprocess += "(BC_1??E1;" + vout
                    + sf.getDiagram().getDuringProcess(sf, sf.getLocations(), "E1");
            lprocess += "BO_1!!(String '''')" + vin + ")*";
            String process = addBCSending(sf, lprocess, 1);
            results.add(process);
            SFIsabelle.processNames.add("P" + sf.getName() + (num++));
        } else if (sf.getDiagram().getCompositeType().equals("AND")
                && !SL2HCSP.isCompact) {
            for (SF_Junction location : sf.getLocations().values()) {
                // skip the locations that are not in this diagram
                if (!sf.getDiagram().inDiagram(location) || !location.isState())
                    continue;
                SF_Diagram diagram = ((SF_State) location).getDiagram();
                int i = ((SF_State) location).getOrder();

                // shared variables
                String vout = "";
                String vin = "";
                // ignore shared variables
//                for (String var : sf.getDiagram().getIvars()) {
//                    vout += "VO" + i + "??" + var + i + ";";
//                    vin += "VI" + i + "!!" + var + i + ";";
//                }
//                for (String var : sf.getDiagram().getOvars()) {
//                    vout += "VO" + i + "??" + var + i + ";";
//                    vin += "VI" + i + "!!" + var + i + ";";
//                }
//                for (String var : sf.getDiagram().getLvars()) {
//                    vout += "VO" + i + "??" + var + i + ";";
//                    vin += "VI" + i + "!!" + var + i + ";";
//                }
//                results.add(SFProcess.delTail(vout));
//                vout = "P" + sf.getName() + num++ + ";";
//                results.add(SFProcess.delTail(vin));
//                vin = ";P" + sf.getName() + num++;

                // initialization
                String pInit = delTail(diagram.getInit(sf.getLocations()));
                ArrayList<String> initT = new ArrayList<String>();
                int start = num;
                while (pInit.length() > 155) {
                    String sub = "";
                    if (pInit.indexOf(";", 150) != -1)
                        sub = pInit.substring(0, pInit.indexOf(";", 150));
                    else {
                        sub = pInit;
                        pInit = "";
                    }
                    sub = addBCSending(sf, sub,
                            ((SF_State) location).getOrder());
                    results.add(sub);
                    num++;
                    pInit = pInit.substring(pInit.indexOf(";", 150) + 1,
                            pInit.length());
                }
                if (pInit.replaceAll(" ", "").replaceAll("\n", "").length() > 0) {
                    pInit = addBCSending(sf, pInit,
                            ((SF_State) location).getOrder());
                    results.add(pInit);
                    num++;
                }
                if (start < num) {
                    String init = "P" + sf.getName() + start;
                    for (int j = start + 1; j < num; j++)
                        init += ";P" + sf.getName() + j;
                    init = addBCSending(sf, init,
                            ((SF_State) location).getOrder());
                    results.add(init);
                    initT.add("P" + sf.getName() + num++);
                    // SFIsabelle.processNames.add("P" + sf.getName() +
                    // (num++));
                }

                // entry of initialization
                String pEntry = SFProcess.delTail(diagram.getEntryProcess(sf
                        .getLocations()));
                if (pEntry.replaceAll(" ", "").replaceAll("\n", "").length() > 0) {
                    pEntry = addBCSending(sf, pEntry,
                            ((SF_State) location).getOrder());
                    results.add(pEntry);
                    initT.add("P" + sf.getName() + num++);
                    // SFIsabelle.processNames.add("P" + sf.getName() +
                    // (num++));
                }

                // change done as initialization
                String done = "done" + i + ":=(Real 0)";
                initT.add(done);

                // during of process
                String pDurings = ((SF_State) location).getDuringProcess(sf,
                        sf.getLocations(), "E" + i);
                // System.out.println(pDurings);
                pDurings = addBCSending(sf, pDurings,
                        ((SF_State) location).getOrder());
                String repT = addList(sf, results, pDurings);

                String totalInit = "";
                for (int i1 = 0; i1 < initT.size(); i1++) {
                    totalInit += initT.get(i1) + ";";
                }
                totalInit = SFProcess.delTail(totalInit);
                results.add(totalInit);
                String totalProc = "P" + sf.getName() + num++ + ";(BC_" + i
                        + "??E" + i + ";(" + vout + repT + ";";
                totalProc += "done" + i + ":=(Real 0));" + "BO_" + i
                        + "!!(String '''')" + vin + ")*";
                results.add(totalProc);
                SFIsabelle.processNames.add("P" + sf.getName() + (num++));
            }
        } else if (sf.getDiagram().getCompositeType().equals("AND")
                && SL2HCSP.isCompact) {
            ArrayList<String> initT = new ArrayList<String>();
            ArrayList<String> repT = new ArrayList<String>();
            int size = 0;
            ArrayList<String> rubbish = new ArrayList<String>();
            for (SF_Junction location : sf.getLocations().values()) {
                // skip the locations that are not in this diagram
                if (!sf.getDiagram().inDiagram(location) || !location.isState())
                    continue;
                size++;
                SF_Diagram diagram = ((SF_State) location).getDiagram();
                // initialization
                String pInit = delTail(diagram.getInit(sf.getLocations()));
                int start = num;
                while (pInit.length() > 155) {
                    String sub = pInit.substring(0, pInit.indexOf(";", 150));
                    sub = addBCSending1(sf, sub);
                    results.add(sub);
                    num++;
                    pInit = pInit.substring(pInit.indexOf(";", 150) + 1,
                            pInit.length());
                }
                if (pInit.replaceAll(" ", "").replaceAll("\n", "").length() > 0) {
                    pInit = addBCSending1(sf, pInit);
                    results.add(pInit);
                    num++;
                }
                if (start < num) {
                    String init = "P" + sf.getName() + start;
                    for (int j = start + 1; j < num; j++)
                        init += ";P" + sf.getName() + j;
                    init = addBCSending1(sf, init);
                    results.add(init);
                    initT.add("P" + sf.getName() + num++);
                    // SFIsabelle.processNames.add("P" + sf.getName() +
                    // (num++));
                }

                // entry of initialization
                String pEntry = SFProcess.delTail(diagram.getEntryProcess(sf
                        .getLocations()));
                if (pEntry.replaceAll(" ", "").replaceAll("\n", "").length() > 0) {
                    pEntry = addBCSending1(sf, pEntry);
                    results.add(pEntry);
                    initT.add("P" + sf.getName() + num++);
                }
                if (((SF_State) location).getName().equals("Train")) {
                    String done = "actl2:=(Real 0);actl2a:=(Real 1)";
                    results.add(done);
                    initT.add("P" + sf.getName() + num++);
                }

                // during of process
                String pDurings = ((SF_State) location).getDuringProcess(sf,
                        sf.getLocations(), "E1");
                // System.out.println(pDurings);
                pDurings = addBCSending1(sf, pDurings);
                String rep = addList(sf, results, pDurings);
                results.add(rep);
                repT.add("P" + sf.getName() + num++);

                // rubbish
                results.add("Skip");
                rubbish.add("P" + sf.getName() + (num++));
            }

            // comms
            ArrayList<String> chIns = new ArrayList<String>();
            for (int i = 1; i <= sf.getDstLines().size(); i++) {
                chIns.add("Ch_" + sf.getDstLine(i).getChName());
            }
            ArrayList<String> chOuts = new ArrayList<String>();
            for (int i = 1; i <= sf.getSrcLines().size(); i++) {
                String chOut = "Ch_" + sf.getName() + "_" + i + "_0";
                chOuts.add(chOut);
            }
            String sending = "";
            String receiving = "";
            String useless = "";
            int usedN = 0;
            String paras = "";
            for (int i = 0; i < chIns.size(); i++) {
                paras += "(";
                receiving += chIns.get(i) + "??"
                        + sf.getDiagram().getIvars().get(i) + ");";
                usedN++;
            }
            for (int i = 0; i < chOuts.size(); i++) {
                sending += chOuts.get(i) + "!!"
                        + sf.getDiagram().getOvars().get(i) + ";";
                useless = chOuts.get(i) + "!!"
                        + sf.getDiagram().getOvars().get(i) + ";";
                usedN++;
            }
            // init
            String totalInit = "";
            for (int i1 = 0; i1 < initT.size(); i1++) {
                totalInit += initT.get(i1) + ";";
            }
            totalInit += "E1:=(String '''');a:=(Real 0);";
            totalInit = SFProcess.delTail(totalInit);
            results.add(totalInit);
            totalInit = "(P" + sf.getName() + num++ + ";"
                    + SFProcess.delTail(sending) + ")";
            // rep
            String st = sf.getParameters().get("st");
            String totalRep = paras + "<(WTrue) && (WTrue)>:(l[=](Real " + st
                    + "));";
            // add useless
            for (int i = usedN; i < Isabelle.commN; i++) {
                sending += useless;
            }
            totalRep += receiving;
            String repTemp = "E1:=(String '''');";
            for (int i1 = 0; i1 < repT.size(); i1++) {
                repTemp += "done1:=(Real 0);" + repT.get(i1) + ";";
            }
            results.add(SFProcess.delTail(repTemp));
            repTemp = "P" + sf.getName() + (num++) + ";";
            totalRep += repTemp + SFProcess.delTail(sending);
            String totalProc = totalInit + ";(" + totalRep + ")*";
            results.add(totalProc);
            SFIsabelle.processNames.add("P" + sf.getName() + (num++));
            for (int j = 1; j <= size; j++) {
                results.add("Skip;" + rubbish.get(j - 1));
                SFIsabelle.processNames.add("P" + sf.getName() + (num++));
            }
        } else {
            System.out.println("A wired stateflow diagram " + sf.getName());
        }
        return results;
    }

    // depth of call
    static int depth = 2;

    protected static String addList(Stateflow sf, ArrayList<String> l1,
                                    String l2) {
        int left = 0;
        int right = 0;
        int mid = 0;
        int times = 0;
        int start = 0;
        String proc = "";
        boolean ifS = false;
        for (int i = 0; i < l2.length(); i++) {
            if (i + 1 < l2.length() && l2.substring(i, i + 2).equals("IF"))
                ifS = true;
            if (l2.substring(i, i + 1).equals("(") && ifS) {
                left++;
            } else if (l2.substring(i, i + 1).equals(")") && ifS) {
                right++;
            }
            if (left == right && left != 0) {
                times++;
                if (times == 1)
                    mid = l2.indexOf("(", i) + 1;
                left = 0;
                right = 0;
            }
            if (times == 2) {
                times = 0;
                String sub = l2.substring(mid, i);
                if (sub.length() > 250) {
                    proc += l2.substring(start, mid) + addList(sf, l1, sub)
                            + ");";
                    // proc += l2.substring(start, mid) + " P"
                    // + sf.getName() + (num - 1) + ");";
                } else {
                    l1.add(l2.substring(start, i + 1));
                    num++;
                    proc += "P" + sf.getName() + (num - 1) + ";";
                }
                start = l2.indexOf(";", i) + 1;
                ifS = false;
            }
        }
        // the whole process
        proc = SFProcess.delTail(proc);
        if (proc.length() > 250)
            proc = addList(sf, l1, proc);

        // put proc in l1 in case that proc is too big
        // l1.add(SFProcess.delTail(proc));
        // proc = "P" + sf.getName() + num++;

        return proc;
    }

    protected static void addList1(Stateflow sf, ArrayList<String> l1, String l2) {
        int left = 0;
        int right = 0;
        int start = 0;
        int mid = 0;
        int times = 0;
        for (int i = 0; i < l2.length(); i++) {
            if (l2.substring(i, i + 1).equals("(")) {
                left++;
            } else if (l2.substring(i, i + 1).equals(")")) {
                right++;
            }
            if (left == right && left != 0) {
                times++;
                if (times == 1)
                    mid = i;
                left = 0;
                right = 0;
            }
            if (times == 2) {
                times = 0;
                String sub = l2.substring(start, i + 1);
                if (sub.length() > 180) {
                    addList(sf, l1,
                            l2.substring(l2.indexOf("(", mid) + 1, i + 1));
                    String highLayer = l2.substring(start, mid + 1) + " P"
                            + sf.getName() + (num - 1);
                    l1.add(highLayer);
                    start = l2.indexOf(";", i) + 1;
                    num++;
                } else {
                    l1.add(sub);
                    start = l2.indexOf(";", i) + 1;
                    num++;
                }
            }
        }
        if (start < l2.length() - 1) {
            String sub = l2.substring(start, l2.length() - 1);
            l1.add(sub);
            num++;
        }
    }

    protected static ArrayList<String> getMonitor(Stateflow sf) {
        ArrayList<String> results = new ArrayList<String>();
        sfNum++;
        sfName.add(sf.getName());
        if (SL2HCSP.isCompact) {
            return results;
        }
        String chTri = "Ch_" + sf.getName() + "_Tri1";
        ArrayList<String> chOuts = new ArrayList<String>();
        for (int i = 1; i <= sf.getSrcLines().size(); i++) {
            String chOut = "Ch_" + sf.getName() + "_" + i + "_0";
            chOuts.add(chOut);
        }
        ArrayList<String> chIns = new ArrayList<String>();
        for (int i = 1; i <= sf.getDstLines().size(); i++) {
            chIns.add("Ch_" + sf.getDstLine(i).getChName());
        }

        // trigger part of the monitor process
        String triger = "";
        if (!sf.getParameters().get("st").equals("-1")) {
            String st = sf.getParameters().get("st");
            triger = "<(WTrue) && (WTrue)>:(l[=](Real " + st + "));";
        } else {
            triger = chTri + "??E;";
        }
        String receiving = "";
        for (int i = 0; i < chIns.size(); i++) {
            triger = "(" + triger;
            receiving += chIns.get(i) + "??" + sf.getDiagram().getIvars().get(i) + ");";
        }
        triger += receiving;

        // main parts of a monitor
        String triProcess = triger + "(num:=(Real 1);empty(EL);(addL EL SE);empty(NL);(addL NL (Real 1)));";
        String monitorF = "IF (num[=](Real 0)) (" + delTail(triProcess) + ")";
        results.add(monitorF);
        num++;

        // size of processes
        int size = SFProcess.getSize(sf);
        // main part of the monitor process
        for (int i = 1; i <= size; i++) {
            // shared variables ignored
            String vout = "";
            String vin = "";
            for (String var : sf.getDiagram().getIvars()) {
                vout += "VO" + i + "!!" + var + ";";
                vin += "VI" + i + "??" + var + ";";
            }
            for (String var : sf.getDiagram().getOvars()) {
                vout += "VO" + i + "!!" + var + ";";
                vin += "VI" + i + "??" + var + ";";
            }
            for (String var : sf.getDiagram().getLvars()) {
                vout += "VO" + i + "!!" + var + ";";
                vin += "VI" + i + "??" + var + ";";
            }
            results.add(SFProcess.delTail(vout));
            vout = ";P" + sf.getName() + num++;
            results.add(SFProcess.delTail(vin));
            vin = ";P" + sf.getName() + num++;
            String monitor = "IF (num[=](Real " + i + ")) (" + "BC_" + i + "!!SE" + vout
                    + " ; ((BR_" + i + "??SE;(addL EL SE);(addL NL (Real 1));num:=(Real 1)) [[ BO_" + i + "??vBO" + i + vin + ");"
                    + "num:=(num[+](Real 1));delL(NL);(addL NL num))";
            results.add(monitor);
            num++;
        }
        String sending = "";
        for (int i = 0; i < chOuts.size(); i++)
            sending += chOuts.get(i) + "!!" + sf.getDiagram().getOvars().get(i) + ";";
        String monitorE = "IF (num[=](Real " + (1 + size)
                + ")) (delL(EL);delL(NL);IF isEmpty(EL) (" + "num:=(Real 0);SE:=(String '''');"
                + SFProcess.delTail(sending + sending) + ");"
                + "IF([~]isEmpty(EL)) (SE:=readL(EL);num:=readL(NL)))";
        results.add(monitorE);
        num++;

        // Initialization
        String pInit = sf.getDiagram().getInit(sf.getLocations());
        String monitor = "";
        if (pInit.replaceAll(" ", "").isEmpty())
            monitor = "(num:=(Real 0);SE:=(String '''');";
        else
            monitor = "((num:=(Real 0);SE:=(String '''');" + SFProcess.delTail(pInit) + ")";
        monitor += ";" + SFProcess.delTail(sending);
        monitor += ");(";
        // repetition started
        for (int i = 1; i <= size + 2; i++) {
            monitor += "P" + sf.getName() + i + ";";
        }
        monitor = delTail(monitor);
        monitor += ")*";
        results.add(monitor);
        SFIsabelle.processNames.add("P" + sf.getName() + (num++));
        return results;
    }

    protected static int getSize(Stateflow sf) {
        if (sf.getDiagram().getCompositeType().equals("AND")) {
            return sf.getDiagram().getSize();
        } else {
            return 1;
        }
    }

    public static String addBCSending(Stateflow sf, String process, int i) {
        // change broadcasting event to message sending
        for (String str : sf.getDiagram().getIEvents()) {
            process = process.replaceAll(";" + str + ";", ";BR_" + i
                    + "!!(String ''" + str + "'');");
            process = process.replaceAll(";" + str + "\\)", ";BR_" + i
                    + "!!(String ''" + str + "''))");
            process = process.replaceAll("\\(" + str + ";", "(BR_" + i
                    + "!!(String ''" + str + "'');");
            process = process.replaceAll("\\(" + str + "\\)", "(BR_" + i
                    + "!!(String ''" + str + "''))");
        }
        for (String str : sf.getDiagram().getLEvents()) {
            process = process.replaceAll(";" + str + ";", ";BR_" + i
                    + "!!(String ''" + str + "'');");
            process = process.replaceAll(";" + str + "\\)", ";BR_" + i
                    + "!!(String ''" + str + "''))");
            process = process.replaceAll("\\(" + str + ";", "(BR_" + i
                    + "!!(String ''" + str + "'');");
            process = process.replaceAll("\\(" + str + "\\)", "(BR_" + i
                    + "!!(String ''" + str + "''))");
        }
        for (String str : sf.getDiagram().getOEvents()) {
            process = process.replaceAll(";" + str + ";", ";BR_" + i
                    + "!!(String ''" + str + "'');");
            process = process.replaceAll(";" + str + "\\)", ";BR_" + i
                    + "!!(String ''" + str + "''))");
            process = process.replaceAll("\\(" + str + ";", "(BR_" + i
                    + "!!(String ''" + str + "'';)");
            process = process.replaceAll("\\(" + str + "\\)", "(BR_" + i
                    + "!!(String ''" + str + "''))");
        }
        return process;
    }

    public static String addBCSending1(Stateflow sf, String process) {
        // change broadcasting event to message sending
        for (String str : sf.getDiagram().getIEvents()) {
            process = process.replaceAll(";" + str + ";", ";E1:="
                    + "(String ''" + str + "'');");
            process = process.replaceAll(";" + str + "\\)", ";E1:="
                    + "(String ''" + str + "''))");
            process = process.replaceAll("\\(" + str + ";", "(E1:="
                    + "(String ''" + str + "'');");
            process = process.replaceAll("\\(" + str + "\\)", "(E1:="
                    + "(String ''" + str + "''))");
        }
        for (String str : sf.getDiagram().getLEvents()) {
            process = process.replaceAll(";" + str + ";", ";E1:="
                    + "(String ''" + str + "'');");
            process = process.replaceAll(";" + str + "\\)", ";E1:="
                    + "(String ''" + str + "''))");
            process = process.replaceAll("\\(" + str + ";", "(E1:="
                    + "(String ''" + str + "'');");
            process = process.replaceAll("\\(" + str + "\\)", "(E1:="
                    + "(String ''" + str + "''))");
        }
        for (String str : sf.getDiagram().getOEvents()) {
            process = process.replaceAll(";" + str + ";", ";E1:="
                    + "(String ''" + str + "'');");
            process = process.replaceAll(";" + str + "\\)", ";E1:="
                    + "(String ''" + str + "''))");
            process = process.replaceAll("\\(" + str + ";", "(E1:="
                    + "(String ''" + str + "'');");
            process = process.replaceAll("\\(" + str + "\\)", "(E1:="
                    + "(String ''" + str + "''))");
        }
        return process;
    }

    // Transform actions on transitions into Isabelle form
    public static String act2Isabelle(String actions) {
        if (actions.contains("Real") || actions.contains("[")) // Isabelle Check
            return actions;
        StringBuilder actions_builder = new StringBuilder(actions);
        // Delete negative numbers: -3.2 -> 0-3.2
        String negative_number_pattern = "[=(><&~] *-\\d+(\\.\\d+)?";
        Pattern p = Pattern.compile(negative_number_pattern);
        Matcher m = p.matcher(actions);
        while (m.find()) {
            int start = m.start();
            int end = m.end();
            String number = actions.substring(start + 1, end);
            actions_builder.replace(start + 1, end, "(0" + number + ")");
            actions = actions_builder.toString();
            m = p.matcher(actions);
        }
        // Transform math operators: + -> [+]
        String operators = "+-*/~";
        int position = 1;
        while (position < actions.length() - 1) {
            String operator = actions.substring(position, position + 1);
            if (operators.contains(operator)) {
                actions_builder.replace(position, position + 1, "[" + operator + "]");
                actions = actions_builder.toString();
                position += 3; // "[+]".length() == 3
            } else
                position++;
        }
        // Transform logic and assignment operators: >= -> [>=], = -> :=
        actions = actions.replaceAll("==", "[EQUAL]");
        actions = actions.replaceAll(">=", "[GREATER_EQUAL]");
        actions = actions.replaceAll("<=", "[LESS_EQUAL]");
        actions = actions.replaceAll("=", ":=");
        actions = actions.replaceAll(">", "[>]");
        actions = actions.replaceAll("<", "[<]");
        actions = actions.replaceAll("GREATER_EQUAL", ">=");
        actions = actions.replaceAll("LESS_EQUAL", "<=");
        actions = actions.replaceAll("EQUAL", "=");
        actions = actions.replaceAll("&+", "[&]");
        actions = actions.replaceAll("\\|+", "[|]");
        // Add parentheses to the right side of := wrt. the predefined priority. For example, x := 1 + 2; -> x := (1 + 2);
        actions_builder = new StringBuilder(actions);
        String assignment_pattern = ":=[^$].*?;";
        p = Pattern.compile(assignment_pattern);
        m = p.matcher(actions);
        while (m.find()) {
            int start = m.start();
            int end = m.end();
            String expression = actions.substring(start + 2, end - 1);
            if (!Pattern.matches(" *\\d+(\\.\\d+)? *", expression)) {
                actions_builder.replace(start + 2, end - 1, "$(" + expression + ")");
            } else {
                actions_builder.replace(start + 2, end - 1, "$" + expression);
            }
            actions = actions_builder.toString();
            m = p.matcher(actions);
        }
        actions = actions.replaceAll("\\$", "");
        // Transform numbers: 10 -> (Real 10)
        actions_builder = new StringBuilder(actions);
        String number_pattern = "[= (\\]]\\d+(\\.\\d+)?";
        p = Pattern.compile(number_pattern);
        m = p.matcher(actions);
        while (m.find()) {
            int start = m.start();
            int end = m.end();
            String number = actions.substring(start + 1, end);
            actions_builder.replace(start + 1, end, "(Real$" + number + ")");
            actions = actions_builder.toString();
            m = p.matcher(actions);
        }
        actions = actions.replaceAll("\\$", " ");

        return actions;
    }

    public static String fun2HCSP(String actions) {
        if (actions.equalsIgnoreCase(""))
            return actions;
        actions = act2Isabelle(actions);
		/*actions = actions.replaceAll(" 1/8", " (RealT)");
		actions = actions.replaceAll("1/2", "(RealTT)");
		actions = actions.replaceAll("=", ":=");
		actions = actions.replaceAll("\\+", "[+]");
		actions = actions.replaceAll("-", "[-]");
		actions = actions.replaceAll("\\*", "[*]");
		actions = actions.replaceAll("/", "[/]");
		actions = actions.replaceAll("\\[\\[\\]\\]", "[=]");
		actions = actions.replaceAll(" 2000", " (Real  2000)");
		actions = actions.replaceAll(" 4000", " (Real  4000)");
		actions = actions.replaceAll(" 32000", " (Real 32000)");
		actions = actions.replaceAll(" 64000", " (Real 64000)");
		actions = actions.replaceAll(" 4", " (Real 4)");
		actions = actions.replaceAll(" 16", " (Real  16)");
		actions = actions.replaceAll(" 14", " (Real  14)");
		actions = actions.replaceAll(" 8", " (Real   8)");
		actions = actions.replaceAll("=6", "= (Real   6)");
		actions = actions.replaceAll(" 105", " (Real 105)");
		actions = actions.replaceAll(" 100", " (Real 100)");
		actions = actions.replaceAll(" 255", " (Real 255)");
		actions = actions.replaceAll(" 250", " (Real 250)");
		actions = actions.replaceAll(" 0", " (Real 0)");
		actions = actions.replaceAll("RealTT", "Real 1/2");
		actions = actions.replaceAll("RealT", "Real 1/8");
		actions = actions.replaceAll("2\\[\\*\\]", "(Real 2)[*]");*/

        return actions;
    }

    public static String act2HCSP(String actions) {
        if (actions.equalsIgnoreCase(""))
            return actions;
        if (!actions.endsWith(";"))
            actions += ";";
        actions = act2Isabelle(actions);
		/*actions = actions.replaceAll("==", "[[]]");
		actions = actions.replaceAll("=", ":=");
		actions = actions.replaceAll("\\[\\[\\]\\]", "[=]");
		actions = actions.replaceAll("=32000", "=(Real 32000)");
		actions = actions.replaceAll("=64000", "=(Real 64000)");
		actions = actions.replaceAll("=14", "=(Real  14)");
		actions = actions.replaceAll("=16", "=(Real  16)");
		actions = actions.replaceAll("=40", "=(Real 40)");
		actions = actions.replaceAll("=45", "=(Real 45)");
		actions = actions.replaceAll(":=1", ":=(Real 1)");
		actions = actions.replaceAll(":=2", ":=(Real 2)");*/
        return actions;
    }

    public static String grd2HCSP(String actions) {
		/*actions = actions.replaceAll("=0", "=(Real 0)");
		actions = actions.replaceAll("=1", "=(Real 1)");
		actions = actions.replaceAll("=2", "=(Real 2)");
		actions = actions.replaceAll("=40", "=(Real 40)");
		actions = actions.replaceAll("=45", "=(Real 45)");
		actions = actions.replaceAll("==", "[=]");
		actions = actions.replaceAll("<=", "fuck");
		actions = actions.replaceAll(">=", "FUCK");
		actions = actions.replaceAll("<", "[<]");
		actions = actions.replaceAll(">", "[>]");
		actions = actions.replaceAll("fuck", "[<=]");
		actions = actions.replaceAll("FUCK", "[>=]");
		actions = actions.replaceAll("&", "[&]");
		actions = actions.replaceAll("\\[>\\]200", "[>](Real 200)");*/
        actions = act2Isabelle(actions);
        return actions;
    }

    public static String delTail(String str) {
        int i = str.lastIndexOf(";");
        if (i == -1)
            return str;
        else
            return str.substring(0, i);
    }

    protected static void printTProcess(Stateflow sf) {
        HashMap<String, SF_Junction> locations = sf.getLocations();
        for (SF_Junction location : locations.values()) {
            if (location.isState() && location.getPath().size() == 1) {
                SF_State s = ((SF_State) location);
                System.out.println(s.getName());
                // System.out.println(s.getEntryProcess(locations));
                System.out.println(s.getDuringProcess(sf, locations, ""));
                // System.out.println(s.getExitProcess(locations));
            }
        }
    }

}
