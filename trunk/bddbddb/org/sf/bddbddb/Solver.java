// Solver.java, created Mar 16, 2004 7:07:16 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.math.BigInteger;
import java.text.DecimalFormat;
import org.sf.bddbddb.util.MyStringTokenizer;
import org.sf.bddbddb.util.Pair;
import org.sf.bddbddb.util.SystemProperties;

/**
 * Solver
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Solver {
    static { SystemProperties.read("solver.properties"); }
    
    boolean NOISY = !System.getProperty("noisy", "yes").equals("no");
    boolean SPLIT_ALL_RULES = false;
    boolean REPORT_STATS = true;
    boolean TRACE = System.getProperty("tracesolve") != null;
    boolean TRACE_FULL = System.getProperty("fulltracesolve") != null;
    boolean PRINT_IR = System.getProperty("printir") != null;
    PrintStream out = System.out;
    
    String basedir = System.getProperty("basedir");
    
    abstract InferenceRule createInferenceRule(List/*<RuleTerm>*/ top, RuleTerm bottom);
    abstract Relation createEquivalenceRelation(Domain fd);
    abstract Relation createNotEquivalenceRelation(Domain fd);
    abstract Relation createRelation(String name, List/*<Attribute>*/ attributes);
    NumberingRule createNumberingRule(InferenceRule ir) {
        return new NumberingRule(this, ir);
    }
    
    Solver() {
        clear();
    }
    
    public void clear() {
        nameToDomain = new HashMap();
        nameToRelation = new HashMap();
        equivalenceRelations = new HashMap();
        notequivalenceRelations = new HashMap();
        rules = new LinkedList();
        relationsToLoad = new LinkedList();
        relationsToLoadTuples = new LinkedList();
        relationsToDump = new LinkedList();
        relationsToDumpNegated = new LinkedList();
        relationsToDumpTuples = new LinkedList();
        relationsToDumpNegatedTuples = new LinkedList();
        relationsToPrintSize = new LinkedList();
        dotGraphsToDump = new LinkedList();
    }
    
    public void initialize() {
        for (Iterator i = nameToRelation.values().iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            r.initialize();
        }
        for (Iterator i = equivalenceRelations.values().iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            r.initialize();
        }
        for (Iterator i = notequivalenceRelations.values().iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            r.initialize();
        }
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            InferenceRule r = (InferenceRule) i.next();
            r.initialize();
        }
    }
    public abstract void solve();
    public abstract void finish();
        
    public Domain getDomain(String name) {
        return (Domain) nameToDomain.get(name);
    }
    
    public Relation getRelation(String name) {
        return (Relation) nameToRelation.get(name);
    }
    
    Map/*<String,Domain>*/ nameToDomain;
    Map/*<String,Relation>*/ nameToRelation;
    Map/*<Domain,Relation>*/ equivalenceRelations;
    Map/*<Domain,Relation>*/ notequivalenceRelations;
    List/*<InferenceRule>*/ rules;
    Collection/*<Relation>*/ relationsToLoad;
    Collection/*<Relation>*/ relationsToLoadTuples;
    Collection/*<Relation>*/ relationsToDump;
    Collection/*<Relation>*/ relationsToDumpNegated;
    Collection/*<Relation>*/ relationsToDumpTuples;
    Collection/*<Relation>*/ relationsToDumpNegatedTuples;
    Collection/*<Relation>*/ relationsToPrintSize;
    Collection/*<Dot>*/ dotGraphsToDump;
    
    public static void main(String[] args) throws IOException, InstantiationException, IllegalAccessException, ClassNotFoundException {
        
        String inputFilename = System.getProperty("datalog");
        if (args.length > 0) inputFilename = args[0];
        
        if (inputFilename == null) {
            printUsage();
            return;
        }
        
        String solverName = System.getProperty("solver", "org.sf.bddbddb.BDDSolver");
        
        Solver dis;
        dis = (Solver) Class.forName(solverName).newInstance();
        
        String sep = System.getProperty("file.separator");
        if (dis.basedir == null) {
            int i = inputFilename.lastIndexOf(sep);
            if (i >= 0) {
                dis.basedir = inputFilename.substring(0, i+1);
            } else {
                i = inputFilename.lastIndexOf("/");
                if (!sep.equals("/") && i >= 0) {
                    dis.basedir = inputFilename.substring(0, i+1);
                } else {
                    dis.basedir = "";
                }
            }
        }
        if (dis.basedir.length() > 0 && !dis.basedir.endsWith(sep) && !dis.basedir.endsWith("/")) {
            dis.basedir += sep;
        }
        
        if (dis.NOISY) dis.out.println("Opening Datalog program \""+inputFilename+"\"");
        MyReader in = new MyReader(new LineNumberReader(new FileReader(inputFilename)));
        dis.readDatalogProgram(in);
        
        if (dis.NOISY) dis.out.println(dis.nameToDomain.size()+" field domains.");
        if (dis.NOISY) dis.out.println(dis.nameToRelation.size()+" relations.");
        if (dis.NOISY) dis.out.println(dis.rules.size()+" rules.");
        
        in.close();
        
        if (dis.NOISY) dis.out.print("Splitting rules: ");
        dis.splitRules();
        if (dis.NOISY) dis.out.println("done.");
        
        if (dis.NOISY) dis.out.print("Initializing solver: ");
        dis.initialize();
        if (dis.NOISY) dis.out.println("done.");
        
        if (dis.PRINT_IR)
            dis.printIR();
        
        if (dis.NOISY) dis.out.print("Loading initial relations: ");
        long time = System.currentTimeMillis();
        dis.loadInitialRelations();
        time = System.currentTimeMillis() - time;
        if (dis.NOISY) dis.out.println("done. ("+time+" ms)");
        
        dis.out.println("Solving: ");
        time = System.currentTimeMillis();
        dis.solve();
        time = System.currentTimeMillis() - time;
        dis.out.println("done. ("+time+" ms)");
        long solveTime = time;
        
        dis.finish();
        
        if (dis.REPORT_STATS) {
            System.out.println("SOLVE_TIME="+solveTime);
            dis.reportStats();
        }
        
        if (dis.NOISY) dis.out.print("Saving results: ");
        time = System.currentTimeMillis();
        dis.saveResults();
        time = System.currentTimeMillis() - time;
        if (dis.NOISY) dis.out.println("done. ("+time+" ms)");
        
    }
    
    public static void printUsage() {
        System.out.println("Usage: java {properties} "+Solver.class.getName()+" <datalog file>");
        System.out.println("System properties:");
        System.out.println("  -Dnoisy           Print rules as they are applied.");
        System.out.println("  -Dtracesolve      Turn on trace information.");
        System.out.println("  -Dfulltracesolve  Also print contents of relations.");
        System.out.println("  -Dsolver          Solver class name.");
        System.out.println("  -Ddatalog         Datalog file name, if not specified on command line.");
        System.out.println("  -Dbddinfo         BDD info file name.");
        System.out.println("  -Dbddvarorder     BDD variable order.");
        System.out.println("  -Dbddnodes        BDD initial node table size.");
        System.out.println("  -Dbddcache        BDD operation cache size.");
        System.out.println("  -Dbddminfree      BDD minimum free parameter.");
        System.out.println("  -Dincremental     Incrementalize all rules by default.");
        System.out.println("  -Dfindbestorder   Find best BDD domain order.");
        System.out.println("  -Ddumpnumberinggraph  Dump the context numbering in dot graph format.");
        System.out.println("  -Ddumprulegraph   Dump the graph of rules in dot format.");
    }
    
    public static class MyReader {
        List readerStack = new LinkedList();
        LineNumberReader current;
        
        public MyReader(LineNumberReader r) {
            current = r;
        }
        
        public void registerReader(LineNumberReader r) {
            if (current != null) readerStack.add(current);
            current = r;
        }
        
        public String readLine() throws IOException {
            String s;
            for (;;) {
                s = current.readLine();
                if (s != null) return s;
                if (readerStack.isEmpty()) return null;
                current = (LineNumberReader) readerStack.remove(readerStack.size()-1);
            }
        }
        
        public int getLineNumber() {
            return current.getLineNumber();
        }
        
        public void close() throws IOException {
            for (;;) {
                current.close();
                if (readerStack.isEmpty()) return;
                current = (LineNumberReader) readerStack.remove(readerStack.size()-1);
            }
        }
    }
    
    static String nextToken(MyStringTokenizer st) {
        String s;
        do {
            s = st.nextToken();
        } while (s.equals(" ") || s.equals("\t"));
        return s;
    }
    
    static String readLine(MyReader in) throws IOException {
        String s = in.readLine();
        if (s == null) return null;
        s = s.trim();
        while (s.endsWith("\\")) {
            String s2 = in.readLine();
            if (s2 == null) break;
            s2 = s2.trim();
            s = s.substring(0, s.length()-1) + s2;
        }
        return s;
    }
    
    void readDatalogProgram(MyReader in) throws IOException {
        for (;;) {
            String s = readLine(in);
            if (s == null) break;
            if (s.length() == 0) continue;
            if (s.startsWith("#")) continue;
            int lineNum = in.getLineNumber();
            if (s.startsWith(".")) {
                // directive
                parseDirective(in, lineNum, s);
                continue;
            }
            MyStringTokenizer st = new MyStringTokenizer(s);
            if (st.hasMoreTokens()) {
                st.nextToken(); // name
                if (st.hasMoreTokens()) {
                    String num = st.nextToken();
                    boolean isNumber;
                    try {
                        new BigInteger(num);
                        isNumber = true;
                    } catch (NumberFormatException x) {
                        isNumber = false;
                    }
                    if (isNumber) {
                        // field domain
                        Domain fd = parseDomain(lineNum, s);
                        if (TRACE) out.println("Parsed field domain "+fd+" size "+fd.size);
                        if (nameToDomain.containsKey(fd.name)) {
                            System.err.println("Error, field domain "+fd.name+" redefined on line "+in.getLineNumber()+", ignoring.");
                        } else {
                            nameToDomain.put(fd.name, fd);
                        }
                        continue;
                    }
                }
            }
            
            if (s.indexOf(".") > 0) {
                // rule
                InferenceRule ir = parseRule(lineNum, s);
                if (TRACE) out.println("Parsed rule "+ir);
                rules.add(ir);
                continue;
            } else {
                // relation
                Relation r = parseRelation(lineNum, s);
                if (TRACE) out.println("Parsed relation "+r);
                if (nameToRelation.containsKey(r.name)) {
                    System.err.println("Error, relation "+r.name+" redefined on line "+in.getLineNumber()+", ignoring.");
                    // Remove relation from lists.
                    deleteRelation(r);
                } else {
                    nameToRelation.put(r.name, r);
                }
                continue;
            }
        }
    }
    
    void outputError(int linenum, int colnum, String line, String msg) {
        System.err.println("Error on line "+linenum+":");
        System.err.println(line);
        while (--colnum >= 0) System.err.print(' ');
        System.err.println("^");
        System.err.println(msg);
    }
    
    void parseDirective(MyReader in, int lineNum, String s) throws IOException {
        if (s.startsWith(".include")) {
            int index = ".include".length()+1;
            String fileName = s.substring(index).trim();
            if (fileName.startsWith("\"")) {
                if (!fileName.endsWith("\"")) {
                    outputError(lineNum, index, s, "Unmatched quotes");
                    throw new IllegalArgumentException();
                }
                fileName = fileName.substring(1, fileName.length()-1);
            }
            in.registerReader(new LineNumberReader(new FileReader(basedir+fileName)));
        } else if (s.startsWith(".split_all_rules")) {
            boolean b = true;
            int index = ".split_all_rules".length()+1;
            if (s.length() > index) {
                String option = s.substring(index).trim();
                b = !option.equals("false");
            }
            SPLIT_ALL_RULES = b;
        } else if (s.startsWith(".report_stats")) {
            boolean b = true;
            int index = ".report_stats".length()+1;
            if (s.length() > index) {
                String option = s.substring(index).trim();
                b = !option.equals("false");
            }
            REPORT_STATS = b;
        } else if (s.startsWith(".noisy")) {
            boolean b = true;
            int index = ".noisy".length()+1;
            if (s.length() > index) {
                String option = s.substring(index).trim();
                b = !option.equals("false");
            }
            NOISY = b;
        } else if (s.startsWith(".bddvarorder")) {
            if (System.getProperty("bddvarorder") == null) {
                int index = ".bddvarorder".length()+1;
                String varOrder = s.substring(index).trim();
                ((BDDSolver) this).VARORDER = varOrder;
            }
        } else if (s.startsWith(".bddnodes")) {
            if (System.getProperty("bddnodes") == null) {
                int index = ".bddnodes".length()+1;
                int n = Integer.parseInt(s.substring(index).trim());
                ((BDDSolver) this).BDDNODES = n;
            }
        } else if (s.startsWith(".bddcache")) {
            if (System.getProperty("bddcache") == null) {
                int index = ".bddcache".length()+1;
                int n = Integer.parseInt(s.substring(index).trim());
                ((BDDSolver) this).BDDCACHE = n;
            }
        } else if (s.startsWith(".bddminfree")) {
            if (System.getProperty("bddminfree") == null) {
                int index = ".bddminfree".length()+1;
                int n = Integer.parseInt(s.substring(index).trim());
                ((BDDSolver) this).BDDMINFREE = n;
            }
        } else if (s.startsWith(".findbestorder")) {
            int index = ".findbestorder".length()+1;
            String val = "";
            if (s.length() > index)
                val = s.substring(index).trim();
            System.setProperty("findbestorder", val);
        } else if (s.startsWith(".incremental")) {
            int index = ".incremental".length()+1;
            String val = "";
            if (s.length() > index)
                val = s.substring(index).trim();
            System.setProperty("incremental", val);
        } else if (s.startsWith(".dot")) {
            int index = ".dot".length()+1;
            String dotSpec = "";
            if (s.length() > index)
                dotSpec = s.substring(index).trim();
            Dot dot = new Dot();
            LineNumberReader lnr = new LineNumberReader(new FileReader(basedir+dotSpec));
            if (TRACE) out.println("Parsing dot "+dotSpec);
            dot.parseInput(this, lnr);
            if (TRACE) out.println("Done parsing dot "+dotSpec);            
            lnr.close();
            dotGraphsToDump.add(dot);
        } else if (s.startsWith(".basedir")) {
            if (System.getProperty("basedir") == null) {
                int index = ".basedir".length()+1;
                String dirName = s.substring(index).trim();
                if (dirName.startsWith("\"") && dirName.endsWith("\"")) {
                    dirName = dirName.substring(1, dirName.length()-1);
                }
                basedir += dirName;
                String sep = System.getProperty("file.separator");
                if (!basedir.endsWith(sep) && !basedir.endsWith("/")) {
                    basedir += sep;
                }
                if (TRACE) out.println("Base directory is now \""+basedir+"\"");
            }
        } else {
            outputError(lineNum, 0, s, "Unknown directive \""+s+"\"");
            throw new IllegalArgumentException();
        }
    }
    
    Domain parseDomain(int lineNum, String s) throws IOException {
        MyStringTokenizer st = new MyStringTokenizer(s);
        String name = nextToken(st);
        String num = nextToken(st);
        long size;
        try {
            size = Long.parseLong(num);
        } catch (NumberFormatException x) {
            outputError(lineNum, st.getPosition(), s, "Expected a number, got \""+num+"\"");
            throw new IllegalArgumentException();
        }
        Domain fd = new Domain(name, size);
        if (st.hasMoreTokens()) {
            String mapName = nextToken(st);
            DataInputStream dis = null;
            try {
                dis = new DataInputStream(new FileInputStream(basedir+mapName));
                fd.loadMap(dis);
            } finally {
                if (dis != null) dis.close();
            }
        }
        return fd;
    }
    
    Relation parseRelation(int lineNum, String s) {
        MyStringTokenizer st = new MyStringTokenizer(s, " \t(:,)", true);
        String name = nextToken(st);
        if (name.indexOf('!') >= 0) {
            outputError(lineNum, st.getPosition(), s, "Relation name cannot contain '!'");
            throw new IllegalArgumentException();
        }
        String openParen = nextToken(st);
        if (!openParen.equals("(")) {
            outputError(lineNum, st.getPosition(), s, "Expected \"(\", got \""+openParen+"\"");
            throw new IllegalArgumentException();
        }
        List attributes = new LinkedList();
        
        for (;;) {
            String fName = nextToken(st);
            String colon = nextToken(st);
            if (!colon.equals(":")) {
                outputError(lineNum, st.getPosition(), s, "Expected \":\", got \""+colon+"\"");
                throw new IllegalArgumentException();
            }
            String fdName = nextToken(st);
            int numIndex = fdName.length() - 1;
            for (;;) {
                char c = fdName.charAt(numIndex);
                if (c < '0' || c > '9') break;
                --numIndex;
                if (numIndex < 0) {
                    outputError(lineNum, st.getPosition(), s, "Expected field domain name, got \""+fdName+"\"");
                    throw new IllegalArgumentException();
                }
            }
            ++numIndex;
            int fdNum = -1;
            if (numIndex < fdName.length()) {
                String number = fdName.substring(numIndex);
                try {
                    fdNum = Integer.parseInt(number);
                } catch (NumberFormatException x) {
                    outputError(lineNum, st.getPosition(), s, "Cannot parse field domain number \""+number+"\"");
                    throw new IllegalArgumentException();
                }
                fdName = fdName.substring(0, numIndex);
            }
            Domain fd = getDomain(fdName);
            if (fd == null) {
                outputError(lineNum, st.getPosition(), s, "Unknown field domain "+fdName);
                throw new IllegalArgumentException();
            }
            String option;
            if (fdNum != -1)
                option = fdName+fdNum;
            else
                option = "";
            attributes.add(new Attribute(fName, fd, option));
            String comma = nextToken(st);
            if (comma.equals(")")) break;
            if (!comma.equals(",")) {
                outputError(lineNum, st.getPosition(), s, "Expected \",\" or \")\", got \""+comma+"\"");
                throw new IllegalArgumentException();
            }
        }
        Relation r = createRelation(name, attributes);
        while (st.hasMoreTokens()) {
            String option = nextToken(st);
            if (option.equals("output")) {
                relationsToDump.add(r);
            } else if (option.equals("outputnot")) {
                relationsToDumpNegated.add(r);
            } else if (option.equals("outputtuples")) {
                relationsToDumpTuples.add(r);
            } else if (option.equals("outputnottuples")) {
                relationsToDumpNegatedTuples.add(r);
            } else if (option.equals("input")) {
                relationsToLoad.add(r);
            } else if (option.equals("inputtuples")) {
                relationsToLoadTuples.add(r);
            } else if (option.equals("printsize")) {
                relationsToPrintSize.add(r);
            } else {
                outputError(lineNum, st.getPosition(), s, "Unexpected option '"+option+"'");
                throw new IllegalArgumentException();
            }
        }
        return r;
    }
    
    void deleteRelation(Relation r) {
        relationsToDump.remove(r);
        relationsToDumpNegated.remove(r);
        relationsToDumpTuples.remove(r);
        relationsToDumpNegatedTuples.remove(r);
        relationsToLoad.remove(r);
        relationsToLoadTuples.remove(r);
        relationsToPrintSize.remove(r);
    }
    
    InferenceRule parseRule(int lineNum, String s) {
        MyStringTokenizer st = new MyStringTokenizer(s, " \t(,/).=!", true);
        Map/*<String,Variable>*/ nameToVar = new HashMap();
        RuleTerm bottom = parseRuleTerm(lineNum, s, nameToVar, st);
        String sep = nextToken(st);
        List/*<RuleTerm>*/ terms = new LinkedList();
        if (!sep.equals(".")) {
            if (!sep.equals(":-")) {
                outputError(lineNum, st.getPosition(), s, "Expected \":-\", got \""+sep+"\"");
                throw new IllegalArgumentException();
            }
            for (;;) {
                RuleTerm rt = parseRuleTerm(lineNum, s, nameToVar, st);
                if (rt == null) break;
                terms.add(rt);
                sep = nextToken(st);
                if (sep.equals(".")) break;
                if (!sep.equals(",")) {
                    outputError(lineNum, st.getPosition(), s, "Expected \".\" or \",\", got \""+sep+"\"");
                    throw new IllegalArgumentException();
                }
            }
        }
        InferenceRule ir = createInferenceRule(terms, bottom);
        ir = parseRuleOptions(lineNum, s, ir, st);
        return ir;
    }
    
    InferenceRule parseRuleOptions(int lineNum, String s, InferenceRule ir, MyStringTokenizer st) {
        while (st.hasMoreTokens()) {
            String option = nextToken(st);
            if (option.equals("split")) {
                if (TRACE) out.println("Splitting rule "+ir);
                ir.split = true;
            } else if (option.equals("number")) {
                if (TRACE) out.println("Rule "+ir+" defines a numbering");
                ir = createNumberingRule(ir);
            } else if (option.equals("cacheafterrename")) {
                BDDInferenceRule r = (BDDInferenceRule) ir;
                r.cache_before_rename = false;
            } else if (option.equals("findbestorder")) {
                BDDInferenceRule r = (BDDInferenceRule) ir;
                r.find_best_order = true;
            } else if (option.equals("trace")) {
                BDDInferenceRule r = (BDDInferenceRule) ir;
                r.TRACE = true;
            } else if (option.equals("tracefull")) {
                BDDInferenceRule r = (BDDInferenceRule) ir;
                r.TRACE = true;
                r.TRACE_FULL = true;
            } else {
                // todo: pri=#, maxiter=#
                outputError(lineNum, st.getPosition(), s, "Unknown rule option \""+option+"\"");
                throw new IllegalArgumentException();
            }
        }
        return ir;
    }
    
    RuleTerm parseRuleTerm(int lineNum, String s, Map/*<String,Variable>*/ nameToVar, MyStringTokenizer st) {
        boolean negated = false;
        String relationName = nextToken(st);
        if (relationName.equals("!")) {
            negated = true;
            relationName = nextToken(st);
        }
        String openParen = nextToken(st);
        boolean flip = false;
        if (openParen.equals("!")) {
            flip = true; openParen = nextToken(st);
        }
        if (openParen.equals("=")) {
            if (negated) {
                outputError(lineNum, st.getPosition(), s, "Unexpected \"!\"");
                throw new IllegalArgumentException();
            }
            
            // "a = b".
            String varName1 = relationName;
            String varName2 = nextToken(st);
            
            Variable var1 = (Variable) nameToVar.get(varName1);
            Variable var2 = (Variable) nameToVar.get(varName2);
            Domain fd;
            if (var1 == null) {
                if (var2 == null) {
                    outputError(lineNum, st.getPosition(), s, "Cannot use \"=\" on two unbound variables.");
                    throw new IllegalArgumentException();
                }
                fd = var2.domain;
                var1 = parseVariable(fd, nameToVar, varName1);
            } else {
                fd = var1.domain;
                if (var2 == null) {
                    var2 = parseVariable(fd, nameToVar, varName2);
                }
            }
            if (var1.domain != var2.domain) {
                outputError(lineNum, st.getPosition(), s, "Variable "+var1+" and "+var2+" have different field domains.");
                throw new IllegalArgumentException();
            }
            
            Relation r = flip ? getNotEquivalenceRelation(fd) : getEquivalenceRelation(fd);
            List vars = new Pair(var1, var2);
            RuleTerm rt = new RuleTerm(vars, r);
            return rt;
        } else if (!openParen.equals("(")) {
            outputError(lineNum, st.getPosition(), s, "Expected \"(\" or \"=\", got \""+openParen+"\"");
            throw new IllegalArgumentException();
        }
        if (flip) {
            outputError(lineNum, st.getPosition(), s, "Unexpected \"!\"");
            throw new IllegalArgumentException();
        }
            
        Relation r = getRelation(relationName);
        if (r == null) {
            outputError(lineNum, st.getPosition(), s, "Unknown relation "+relationName);
            throw new IllegalArgumentException();
        }
        if (negated) r = r.makeNegated(this);
        List/*<Variable>*/ vars = new LinkedList();
        for (;;) {
            if (r.attributes.size() <= vars.size()) {
                outputError(lineNum, st.getPosition(), s, "Too many fields for "+r);
                throw new IllegalArgumentException();
            }
            Attribute a = (Attribute) r.attributes.get(vars.size());
            Domain fd = a.attributeDomain;
            String varName = nextToken(st);
            Variable var = parseVariable(fd, nameToVar, varName);
            if (false && vars.contains(var)) { // temporarily disabled to handle "number" rules.
                outputError(lineNum, st.getPosition(), s, "Duplicate variable "+var);
                throw new IllegalArgumentException();
            }
            vars.add(var);
            if (var.domain == null) var.domain = fd;
            else if (var.domain != fd) {
                outputError(lineNum, st.getPosition(), s, "Variable "+var+" used as both "+var.domain+" and "+fd);
                throw new IllegalArgumentException();
            }
            String sep = nextToken(st);
            if (sep.equals(")")) break;
            if (!sep.equals(",")) {
                outputError(lineNum, st.getPosition(), s, "Expected ',' or ')', got '"+sep+"'");
                throw new IllegalArgumentException();
            }
        }
        if (r.attributes.size() != vars.size()) {
            outputError(lineNum, st.getPosition(), s, "Wrong number of vars in rule term for "+relationName);
            throw new IllegalArgumentException();
        }
        
        RuleTerm rt = new RuleTerm(vars, r);
        return rt;
    }
    
    Variable parseVariable(Domain fd, Map nameToVar, String varName) {
        char firstChar = varName.charAt(0);
        Variable var;
        if (firstChar >= '0' && firstChar <= '9') {
            var = new Constant(Long.parseLong(varName));
        } else if (firstChar == '"') {
            String namedConstant = varName.substring(1, varName.length()-1);
            var = new Constant(fd.namedConstant(namedConstant));
        } else if (!varName.equals("_")) {
            var = (Variable) nameToVar.get(varName);
            if (var == null) nameToVar.put(varName, var = new Variable(varName));
        } else {
            var = new Variable();
        }
        if (var.domain == null) var.domain = fd;
        return var;
    }
    
//    public Relation getOrCreateRelation(String name, List/*<Variable>*/ vars) {
//        Relation r = (Relation) nameToRelation.get(name);
//        if (r == null) nameToRelation.put(name, r = createRelation(name, vars));
//        return r;
//    }
    
    Relation getEquivalenceRelation(Domain fd) {
        Relation r = (Relation) equivalenceRelations.get(fd);
        if (r == null) {
            equivalenceRelations.put(fd, r = createEquivalenceRelation(fd));
        }
        return r;
    }
    
    Relation getNotEquivalenceRelation(Domain fd) {
        Relation r = (Relation) notequivalenceRelations.get(fd);
        if (r == null) {
            notequivalenceRelations.put(fd, r = createNotEquivalenceRelation(fd));
        }
        return r;
    }
    
    void loadInitialRelations() throws IOException {
        for (Iterator i = relationsToLoad.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            try {
                r.load();
            } catch (IOException x) {
                System.out.println("WARNING: Cannot load bdd "+r+": "+x.toString());
            }
        }
        for (Iterator i = relationsToLoadTuples.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            try {
                r.loadTuples();
            } catch (IOException x) {
                System.out.println("WARNING: Cannot load tuples "+r+": "+x.toString());
            }
        }
    }
    
    void splitRules() {
        List newRules = new LinkedList();
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            InferenceRule r = (InferenceRule) i.next();
            if (SPLIT_ALL_RULES || r.split)
                newRules.addAll(r.split(rules.indexOf(r)));
        }
        rules.addAll(newRules);
    }
    
    void reportStats() {
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            InferenceRule r = (InferenceRule) i.next();
            r.reportStats();
        }
    }
    
    void saveResults() throws IOException {
        for (Iterator i = relationsToPrintSize.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            double size = r.dsize();
            DecimalFormat myFormatter = new DecimalFormat("0.");
            String output = myFormatter.format(size); 
            out.println("SIZE OF "+r+": "+output);
        }
        for (Iterator i = relationsToDump.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping BDD for "+r);
            r.save();
        }
        for (Iterator i = relationsToDumpNegated.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping negated BDD for "+r);
            r.saveNegated();
        }
        for (Iterator i = relationsToDumpTuples.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping tuples for "+r);
            r.saveTuples();
        }
        for (Iterator i = relationsToDumpNegatedTuples.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping negated tuples for "+r);
            r.saveNegatedTuples();
        }
        for (Iterator i = dotGraphsToDump.iterator(); i.hasNext(); ) {
            Dot dot = (Dot) i.next();
            if (NOISY) out.println("Dumping dot graph");
            dot.outputGraph();
        }
    }

    void printIR() {
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            InferenceRule ir = (InferenceRule) i.next();
            System.out.println(ir);
            List instr = ir.generateIR();
            for (Iterator j = instr.iterator(); j.hasNext(); ) {
                System.out.println(j.next());
            }
            System.out.println();
        }
    }
}
