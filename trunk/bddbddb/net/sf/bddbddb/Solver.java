// Solver.java, created Mar 16, 2004 7:07:16 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.math.BigInteger;
import java.net.URL;
import java.text.DecimalFormat;
import jwutil.classloader.HijackingClassLoader;
import jwutil.collections.GenericMultiMap;
import jwutil.collections.IndexMap;
import jwutil.collections.MultiMap;
import jwutil.collections.Pair;
import jwutil.io.SystemProperties;
import jwutil.reflect.Reflect;
import jwutil.strings.MyStringTokenizer;
import jwutil.util.Assert;
import net.sf.bddbddb.InferenceRule.DependenceNavigator;
import net.sf.bddbddb.dataflow.PartialOrder.BeforeConstraint;
import net.sf.bddbddb.dataflow.PartialOrder.InterleavedConstraint;
import net.sf.bddbddb.ir.IR;

/**
 * Solver
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Solver {
    static {
        SystemProperties.read("solver.properties");
    }
    
    /** Print rules as they are triggered. */
    boolean NOISY = !System.getProperty("noisy", "yes").equals("no");
    /** Split all rules. */
    boolean SPLIT_ALL_RULES = !System.getProperty("split_all_rules", "no").equals("no");
    /** Split no rules, even if they have a "split" keyword. */
    boolean SPLIT_NO_RULES = !System.getProperty("split_no_rules", "no").equals("no");
    /** Report the stats for each rule at the end. */
    boolean REPORT_STATS = true;
    /** Trace the solver. */
    boolean TRACE = System.getProperty("tracesolve") != null;
    /** Do a full trace, even dumping the contents of relations. */
    boolean TRACE_FULL = System.getProperty("fulltracesolve") != null;
    /** Use the IR rather than the rules. */
    boolean USE_IR = !System.getProperty("useir", "no").equals("no");
    /** Print the IR before interpreting it. */
    boolean PRINT_IR = System.getProperty("printir") != null;
    
    boolean LEARN_ALL_RULES = !System.getProperty("learnbestorder", "no").equals("no");
    boolean LEARN_BEST_ORDER = !System.getProperty("learnbestorder", "no").equals("no");
    /** Trace output stream. */
    PrintStream out = System.out;
    
    /** Input Datalog filename. */
    String inputFilename;
    /** Base directory where to load/save files. */
    String basedir = System.getProperty("basedir");
    /** Include directories. */
    String includedirs = System.getProperty("includedirs");
    /** List of paths to search when loading files. */
    List/*<String>*/ includePaths;
    /** Map between id numbers and relations. */
    IndexMap/*<Relation>*/ relations;
    /** Map between names and domains. */
    Map/*<String,Domain>*/ nameToDomain;
    /** Map between names and relations. */
    Map/*<String,Relation>*/ nameToRelation;
    /** Map between domains and equivalence relations. */
    MultiMap/*<Pair<Domain,Domain>,Relation>*/ equivalenceRelations;
    /** Map between domains and less than relations. */
    MultiMap/*<Pair<Domain,Domain>,Relation>*/ lessThanRelations;
    /** Map between domains and greater than relations. */
    MultiMap/*<Pair<Domain,Domain>,Relation>*/ greaterThanRelations;
    /** Map between domains and equivalence relations. */
    Map/*<Pair<Domain,Domain>,Relation>*/ mapRelations;
    /** List of inference rules. */
    List/*<InferenceRule>*/ rules;
    /** Iteration order. */
    IterationFlowGraph ifg;

    /** Flag that is set on initialization. */
    boolean isInitialized;
    
    Collection/*<Relation>*/ relationsToLoad;
    Collection/*<Relation>*/ relationsToLoadTuples;
    Collection/*<Relation>*/ relationsToDump;
    Collection/*<Relation>*/ relationsToDumpTuples;
    Collection/*<Relation>*/ relationsToPrintTuples;
    Collection/*<Relation>*/ relationsToPrintSize;
    Collection/*<Dot>*/ dotGraphsToDump;

    /**
     * Create a new inference rule.
     * 
     * @param top  list of subgoals of rule
     * @param bottom  head of rule
     * @return  new inference rule
     */
    abstract InferenceRule createInferenceRule(List/*<RuleTerm>*/ top, RuleTerm bottom);

    /**
     * Create a new equivalence relation.
     * 
     * @param fd1  first domain of relation
     * @param fd2  second domain of relation
     * @return  new equivalence relation
     */
    abstract Relation createEquivalenceRelation(Domain fd1, Domain fd2);

    /**
     * Create a new less-than relation.
     * 
     * @param fd1  first domain of relation
     * @param fd2  second domain of relation
     * @return  new equivalence relation
     */
    abstract Relation createLessThanRelation(Domain fd1, Domain fd2);

    /**
     * Create a new greater-than relation.
     * 
     * @param fd1  first domain of relation
     * @param fd2  second domain of relation
     * @return  new equivalence relation
     */
    abstract Relation createGreaterThanRelation(Domain fd1, Domain fd2);

    /**
     * Create a new map relation.
     * 
     * @param fd1  first domain of relation
     * @param fd2  second domain of relation
     * @return  new map relation
     */
    abstract Relation createMapRelation(Domain fd1, Domain fd2);
    
    /**
     * Create a new relation.
     * 
     * @param name  name of relation
     * @param attributes  attributes of relation
     * @return  new relation
     */
    public abstract Relation createRelation(String name, List/*<Attribute>*/ attributes);

    /**
     * Register the given relation with this solver.
     * 
     * @param r  relation to register
     */
    void registerRelation(Relation r) {
        int i = relations.get(r);
        Assert._assert(i == relations.size() - 1);
        Assert._assert(i == r.id);
        Object old = nameToRelation.put(r.name, r);
        Assert._assert(old == null);
    }

    /**
     * Create a numbering rule from the given rule template.
     * 
     * @param ir  incoming rule
     * @return  new numbering rule
     */
    NumberingRule createNumberingRule(InferenceRule ir) {
        return new NumberingRule(this, ir);
    }

    /**
     * Construct a solver object.
     */
    protected Solver() {
        clear();
    }

    /**
     * Clear this solver of all relations, domains, and rules.
     */
    public void clear() {
        relations = new IndexMap("relations");
        nameToDomain = new HashMap();
        nameToRelation = new HashMap();
        equivalenceRelations = new GenericMultiMap();
        greaterThanRelations = new GenericMultiMap();
        lessThanRelations = new GenericMultiMap();
        mapRelations = new HashMap();
        rules = new LinkedList();
        relationsToLoad = new LinkedList();
        relationsToLoadTuples = new LinkedList();
        relationsToDump = new LinkedList();
        relationsToDumpTuples = new LinkedList();
        relationsToPrintTuples = new LinkedList();
        relationsToPrintSize = new LinkedList();
        dotGraphsToDump = new LinkedList();
    }

    /**
     * Initialize all of the relations and rules.
     */
    public void initialize() {
        for (Iterator i = nameToRelation.values().iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            r.initialize();
        }
        for (Iterator i = rules.iterator(); i.hasNext();) {
            InferenceRule r = (InferenceRule) i.next();
            r.initialize();
        }
    }

    Stratify stratify;
    IR ir;
    
    /**
     * Stratify the rules.
     */
    public void stratify(boolean noisy) {
        stratify = new Stratify(this);
        stratify.NOISY = noisy;
        stratify.stratify();
        
        if (USE_IR) {
            ir = IR.create(stratify);
            ifg = ir.graph;
            ir.optimize();
            if (PRINT_IR) ir.printIR();
        } else {
            ifg = new IterationFlowGraph(rules, stratify);
            //IterationList list = ifg.expand();
        }
    }
    
    /**
     * Solve the rules.
     */
    public abstract void solve();

    /**
     * Called after solving.
     */
    public abstract void finish();
    
    /**
     * Clean up the solver, freeing the memory associated with it.
     */
    public abstract void cleanup();

    /**
     * Get the named domain.
     * 
     * @param name  domain name
     * @return  domain that has the name
     */
    public Domain getDomain(String name) {
        return (Domain) nameToDomain.get(name);
    }

    /**
     * Get the named relation.
     * 
     * @param name  relation name
     * @return  relation that has the name
     */
    public Relation getRelation(String name) {
        return (Relation) nameToRelation.get(name);
    }

    /**
     * Get the relation with the given index.
     * 
     * @param index  index desired
     * @return  relation
     */
    public Relation getRelation(int index) {
        return (Relation) relations.get(index);
    }
    
    public IndexMap getRelations(){ return relations; }

    static void addAllValues(Collection c, MultiMap m) {
        for (Iterator i = m.keySet().iterator(); i.hasNext(); ) {
            c.addAll(m.getValues(i.next()));
        }
    }
    
    /**
     * Get all the equivalence relations.
     * 
     * @return  collection of equivalence relations
     */
    public Collection getComparisonRelations() {
        Collection set = new LinkedList();
        addAllValues(set, equivalenceRelations);
        addAllValues(set, lessThanRelations);
        addAllValues(set, greaterThanRelations);
        set.addAll(mapRelations.values());
        return set;
    }
    
    /**
     * Get the base directory used for output.
     * 
     * @return  base directory used for output
     */
    public String getBaseDir() {
        return basedir;
    }
    
    /**
     * Initialize the basedir variable, given the specified input Datalog filename.
     * 
     * @param inputFilename  input Datalog filename
     */
    void initializeBasedir(String inputFilename) {
        String sep = System.getProperty("file.separator");
        if (basedir == null) {
            int i = inputFilename.lastIndexOf(sep);
            if (i >= 0) {
                basedir = inputFilename.substring(0, i + 1);
            } else {
                i = inputFilename.lastIndexOf("/");
                if (!sep.equals("/") && i >= 0) {
                    basedir = inputFilename.substring(0, i + 1);
                } else {
                    basedir = "";
                }
            }
        }
        if (basedir.length() > 0 && !basedir.endsWith(sep) && !basedir.endsWith("/")) {
            basedir += sep;
        }
        if (includedirs == null) includedirs = basedir;
    }
    
    public void load(String filename) throws IOException, InstantiationException, IllegalAccessException, ClassNotFoundException {
        inputFilename = filename;
        if (NOISY) out.println("Opening Datalog program \"" + inputFilename + "\"");
        MyReader in = new MyReader(new LineNumberReader(new FileReader(inputFilename)));
        initializeBasedir(inputFilename);
        load(in);
    }
    
    public void load(MyReader in) throws IOException, InstantiationException, IllegalAccessException, ClassNotFoundException {
        readDatalogProgram(in);
        if (NOISY) out.println(nameToDomain.size() + " field domains.");
        if (NOISY) out.println(nameToRelation.size() + " relations.");
        if (NOISY) out.println(rules.size() + " rules.");
        in.close();
        if (NOISY) out.print("Splitting rules: ");
        splitRules();
        if (NOISY) out.println("done.");
        //out.print("Magic Set Transformation: ");
        //MagicSetTransformation mst = new MagicSetTransformation(this);
        //mst.transform(rules);
        //out.println("done.");
        if (NOISY) out.print("Initializing solver: ");
        initialize();
        if (NOISY) out.println("done.");
        if (NOISY) out.print("Loading initial relations: ");
        long time = System.currentTimeMillis();
        loadInitialRelations();
        time = System.currentTimeMillis() - time;
        if (NOISY) out.println("done. (" + time + " ms)");
        out.println("Stratifying: ");
        time = System.currentTimeMillis();
        stratify(true);
        time = System.currentTimeMillis() - time;
        out.println("done. (" + time + " ms)");
        out.println("Solving: ");
    }
    public long startTime;
    public void run() {
        startTime = System.currentTimeMillis();
        solve();
        long solveTime = System.currentTimeMillis() - startTime;
        out.println("done. (" + solveTime + " ms)");
      
        finish();
        if (REPORT_STATS) {
            System.out.println("SOLVE_TIME=" + solveTime);
            reportStats();
        }
    }
    
    public void save() throws IOException {
        if (NOISY) out.print("Saving results: ");
        long time = System.currentTimeMillis();
        saveResults();
        time = System.currentTimeMillis() - time;
        if (NOISY) out.println("done. (" + time + " ms)");
        cleanup();
    }
    
    /**
     * The entry point to the application.
     * 
     * @param args  command line arguments
     * @throws IOException
     * @throws InstantiationException
     * @throws IllegalAccessException
     * @throws ClassNotFoundException
     */
    public static void main2(String[] args) throws IOException, InstantiationException, IllegalAccessException, ClassNotFoundException {
        String inputFilename = System.getProperty("datalog");
        if (args.length > 0) inputFilename = args[0];
        if (inputFilename == null) {
            printUsage();
            return;
        }
        String solverName = System.getProperty("solver", "net.sf.bddbddb.BDDSolver");
        Solver dis;
        dis = (Solver) Class.forName(solverName).newInstance();
        dis.load(inputFilename);
        dis.run();
        dis.save();
    }

    /**
     * Print usage information.
     */
    public static void printUsage() {
        System.out.println("Usage: java {properties} " + Solver.class.getName() + " <datalog file>");
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
        System.out.println("  -Duseir           Compile rules using intermediate representation.");
        System.out.println("  -Dprintir         Print intermediate representation before interpreting.");
    }
    
    /**
     * A LineNumberReader that can nest through multiple included files.
     * 
     * @author John Whaley
     * @version $Id$
     */
    public static class MyReader {
        /**
         * Stack of readers, to handle including files.
         */
        List readerStack = new LinkedList();
        /**
         * Current line number reader.
         */
        LineNumberReader current;

        /**
         * Construct a new reader from the given line number reader.
         * 
         * @param r  reader
         */
        public MyReader(LineNumberReader r) {
            current = r;
        }

        /**
         * Register a new reader, pushing the current one on the stack.
         * 
         * @param r  reader to register
         */
        public void registerReader(LineNumberReader r) {
            if (current != null) readerStack.add(current);
            current = r;
        }

        /**
         * Read a line.  If the current reader is empty, we pop one off the stack.
         * If it is empty and the stack is empty, returns null.
         * 
         * @return  the line that was read
         * @throws IOException
         */
        public String readLine() throws IOException {
            String s;
            for (;;) {
                s = current.readLine();
                if (s != null) return s;
                if (readerStack.isEmpty()) return null;
                current = (LineNumberReader) readerStack.remove(readerStack.size() - 1);
            }
        }

        /**
         * Return the line number in the current reader.
         * 
         * @return  line number
         */
        public int getLineNumber() {
            return current.getLineNumber();
        }

        /**
         * Close all of the readers we have open.
         * 
         * @throws IOException
         */
        public void close() throws IOException {
            for (;;) {
                current.close();
                if (readerStack.isEmpty()) return;
                current = (LineNumberReader) readerStack.remove(readerStack.size() - 1);
            }
        }
    }

    /**
     * Get the next token, skipping over spaces.
     * 
     * @param st  string tokenizer
     * @return  next non-space token
     */
    static String nextToken(MyStringTokenizer st) {
        String s;
        do {
            s = st.nextToken();
        } while (s.equals(" ") || s.equals("\t"));
        return s;
    }

    /**
     * Utility function to read a line from the given reader.
     * Allows line wrapping using backslashes, among other things.
     * 
     * @param in  input reader
     * @return  line
     * @throws IOException
     */
    static String readLine(MyReader in) throws IOException {
        String s = in.readLine();
        if (s == null) return null;
        s = s.trim();
        while (s.endsWith("\\")) {
            String s2 = in.readLine();
            if (s2 == null) break;
            s2 = s2.trim();
            s = s.substring(0, s.length() - 1) + s2;
        }
        return s;
    }

    /**
     * Read and parse a Datalog program.
     * 
     * @param inputFilename  name of file to read
     * @throws IOException
     */
    public void readDatalogProgram(String inputFilename) throws IOException {
        MyReader in = null;
        try {
            in = new MyReader(new LineNumberReader(new FileReader(inputFilename)));
            readDatalogProgram(in);
        } finally {
            if (in != null) try { in.close(); } catch (IOException _) { }
        }
    }
    
    /**
     * Read and parse a Datalog program.
     * 
     * @param in  input reader
     * @throws IOException
     */
    public void readDatalogProgram(MyReader in) throws IOException {
        for (;;) {
            String s = readLine(in);
            if (s == null) break;
            parseDatalogLine(s, in);
        }
    }
    
    /**
     * Parse a line from a Datalog program.
     * 
     * @param s  line to parse
     * @param in  input reader
     * @return  the rule, relation, domain, or list of rules we parsed, or null
     * @throws IOException
     */
    Object parseDatalogLine(String s, MyReader in) throws IOException {
        if (s.length() == 0) return null;
        if (s.startsWith("#")) return null;
        int lineNum = in.getLineNumber();
        if (s.startsWith(".")) {
            // directive
            parseDirective(in, lineNum, s);
            return null;
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
                    if (TRACE) out.println("Parsed field domain " + fd + " size " + fd.size);
                    if (nameToDomain.containsKey(fd.name)) {
                        System.err.println("Error, field domain " + fd.name + " redefined on line " + in.getLineNumber() + ", ignoring.");
                    } else {
                        nameToDomain.put(fd.name, fd);
                    }
                    return fd;
                }
            }
        }
        int dotIndex = s.indexOf('.');
        int braceIndex = s.indexOf('{');
        int qIndex = s.indexOf('?');
        if (dotIndex > 0 && (braceIndex == -1 || dotIndex < braceIndex)) {
            // rule
            InferenceRule ir = parseRule(lineNum, s);
            if (TRACE) out.println("Parsed rule " + ir);
            rules.add(ir);
            return Collections.singletonList(ir);
        } else if (qIndex > 0 && (braceIndex == -1 || qIndex < braceIndex)) {
            // query
            List/*<InferenceRule>*/ ir = parseQuery(lineNum, s);
            if (ir != null) {
                if (TRACE) out.println("Parsed query " + ir);
                rules.addAll(ir);
            }
            return ir;
        } else {
            // relation
            Relation r = parseRelation(lineNum, s);
            if (TRACE && r != null) out.println("Parsed relation " + r);
            return r;
        }
    }

    /**
     * Output a parse error at the given location.
     * 
     * @param linenum  line number of error
     * @param colnum  column number of error
     * @param line  text of line containing error
     * @param msg  error message
     */
    void outputError(int linenum, int colnum, String line, String msg) {
        System.err.println("Error on line " + linenum + ":");
        System.err.println(line);
        while (--colnum >= 0)
            System.err.print(' ');
        System.err.println("^");
        System.err.println(msg);
    }

    /**
     * Parse a directive.
     * 
     * @param in  input reader
     * @param lineNum  current line number, for debugging purposes
     * @param s  string containing directive to parse
     * @throws IOException
     */
    void parseDirective(MyReader in, int lineNum, String s) throws IOException {
        if (s.startsWith(".include")) {
            int index = ".include".length() + 1;
            String fileName = s.substring(index).trim();
            if (fileName.startsWith("\"")) {
                if (!fileName.endsWith("\"")) {
                    outputError(lineNum, index, s, "Unmatched quotes");
                    throw new IllegalArgumentException();
                }
                fileName = fileName.substring(1, fileName.length() - 1);
            }
            if (!fileName.startsWith("/")) {
                String[] dirs = includedirs.split(System.getProperty("path.separator"));
                for (int i=0; i<dirs.length; i++) {
                    if ((new File(dirs[i],fileName)).exists()) {
                        fileName = dirs[i]+System.getProperty("file.separator")+fileName;
                        break;
                    }
                }
            }
            in.registerReader(new LineNumberReader(new FileReader(fileName)));
        } else if (s.startsWith(".split_all_rules")) {
            boolean b = true;
            int index = ".split_all_rules".length() + 1;
            if (s.length() > index) {
                String option = s.substring(index).trim();
                b = !option.equals("false");
            }
            SPLIT_ALL_RULES = b;
        } else if (s.startsWith(".report_stats")) {
            boolean b = true;
            int index = ".report_stats".length() + 1;
            if (s.length() > index) {
                String option = s.substring(index).trim();
                b = !option.equals("false");
            }
            REPORT_STATS = b;
        } else if (s.startsWith(".noisy")) {
            boolean b = true;
            int index = ".noisy".length() + 1;
            if (s.length() > index) {
                String option = s.substring(index).trim();
                b = !option.equals("false");
            }
            NOISY = b;
        } else if (s.startsWith(".trace")) {
            boolean b = true;
            int index = ".trace".length() + 1;
            if (s.length() > index) {
                String option = s.substring(index).trim();
                b = !option.equals("false");
            }
            TRACE = b;
        } else if (s.startsWith(".bddvarorder")) {
            if (System.getProperty("bddvarorder") == null) {
                int index = ".bddvarorder".length() + 1;
                String varOrder = s.substring(index).trim();
                ((BDDSolver) this).VARORDER = varOrder;
            }
        } else if (s.startsWith(".bddnodes")) {
            if (System.getProperty("bddnodes") == null) {
                int index = ".bddnodes".length() + 1;
                int n = Integer.parseInt(s.substring(index).trim());
                ((BDDSolver) this).BDDNODES = n;
            }
        } else if (s.startsWith(".bddcache")) {
            if (System.getProperty("bddcache") == null) {
                int index = ".bddcache".length() + 1;
                int n = Integer.parseInt(s.substring(index).trim());
                ((BDDSolver) this).BDDCACHE = n;
            }
        } else if (s.startsWith(".bddminfree")) {
            if (System.getProperty("bddminfree") == null) {
                int index = ".bddminfree".length() + 1;
                double n = Double.parseDouble(s.substring(index).trim());
                ((BDDSolver) this).BDDMINFREE = n;
            }
        } else if (s.startsWith(".findbestorder")) {
            int index = ".findbestorder".length() + 1;
            String val = "";
            if (s.length() > index) val = s.substring(index).trim();
            System.setProperty("findbestorder", val);
        }else if (s.startsWith(".learnbestorder")){
            int index = ".learnbestorder".length() + 1;
            String val = "";
            if (s.length() > index) val = s.substring(index).trim();
            LEARN_BEST_ORDER = true;
            LEARN_ALL_RULES = true;
            System.setProperty("learnbestorder", val);
        } else if (s.startsWith(".incremental")) {
            int index = ".incremental".length() + 1;
            String val = "";
            if (s.length() > index) val = s.substring(index).trim();
            System.setProperty("incremental", val);
        } else if (s.startsWith(".dot")) {
            int index = ".dot".length() + 1;
            String dotSpec = "";
            if (s.length() > index) dotSpec = s.substring(index).trim();
            Dot dot = new Dot();
            LineNumberReader lnr = new LineNumberReader(new FileReader(basedir + dotSpec));
            if (TRACE) out.println("Parsing dot " + dotSpec);
            dot.parseInput(this, lnr);
            if (TRACE) out.println("Done parsing dot " + dotSpec);
            lnr.close();
            dotGraphsToDump.add(dot);
        } else if (s.startsWith(".basedir")) {
            if (System.getProperty("basedir") == null) {
                int index = ".basedir".length() + 1;
                String dirName = s.substring(index).trim();
                if (dirName.startsWith("\"") && dirName.endsWith("\"")) {
                    dirName = dirName.substring(1, dirName.length() - 1);
                }
                basedir += dirName;
                String sep = System.getProperty("file.separator");
                if (!basedir.endsWith(sep) && !basedir.endsWith("/")) {
                    basedir += sep;
                }
                if (TRACE) out.println("Base directory is now \"" + basedir + "\"");
                Assert._assert(includedirs != null);
                includedirs += System.getProperty("path.separator") + basedir;
            }
        } else {
            outputError(lineNum, 0, s, "Unknown directive \"" + s + "\"");
            throw new IllegalArgumentException();
        }
    }

    /**
     * Parse a domain declaration.
     * 
     * @param lineNum  current line number for outputting error messages
     * @param s  string containing relation declaration
     * @return  new domain 
     */
    Domain parseDomain(int lineNum, String s) {
        MyStringTokenizer st = new MyStringTokenizer(s);
        String name = nextToken(st);
        String num = nextToken(st);
        long size;
        try {
            size = Long.parseLong(num);
        } catch (NumberFormatException x) {
            outputError(lineNum, st.getPosition(), s, "Expected a number, got \"" + num + "\"");
            throw new IllegalArgumentException();
        }
        Domain fd = new Domain(name, size);
        if (st.hasMoreTokens()) {
            String mapName = nextToken(st);
            BufferedReader dis = null;
            try {
                dis = new BufferedReader(new FileReader(basedir + mapName));
                fd.loadMap(dis);
            } catch (IOException x) {
                System.err.println("WARNING: Cannot load mapfile \"" + basedir + mapName + "\", skipping.");
            } finally {
                if (dis != null) try { dis.close(); } catch (IOException x) { }
            }
        }
        return fd;
    }

    static final char[] badchars = new char[] { '!', '=', ':', '-', '<', '>', '(', ')', ',', ' ', '\t', '\f' };
    
    /**
     * Parse a relation declaration.
     * 
     * @param lineNum  current line number for outputting error messages
     * @param s  string containing relation declaration
     * @return  new relation, or null if the relation was already defined
     */
    Relation parseRelation(int lineNum, String s) {
        MyStringTokenizer st = new MyStringTokenizer(s, " \t(:,)", true);
        String name = nextToken(st);
        for (int i = 0; i < badchars.length; ++i) {
            if (name.indexOf(badchars[i]) >= 0) {
                outputError(lineNum, st.getPosition(), s, "Relation name cannot contain '"+badchars[i]+"'");
                throw new IllegalArgumentException();
            }
        }
        String openParen = nextToken(st);
        if (!openParen.equals("(")) {
            outputError(lineNum, st.getPosition(), s, "Expected \"(\", got \"" + openParen + "\"");
            throw new IllegalArgumentException();
        }
        List attributes = new LinkedList();
        for (;;) {
            String fName = nextToken(st);
            String colon = nextToken(st);
            if (!colon.equals(":")) {
                outputError(lineNum, st.getPosition(), s, "Expected \":\", got \"" + colon + "\"");
                throw new IllegalArgumentException();
            }
            String fdName = nextToken(st);
            int numIndex = fdName.length() - 1;
            for (;;) {
                char c = fdName.charAt(numIndex);
                if (c < '0' || c > '9') break;
                --numIndex;
                if (numIndex < 0) {
                    outputError(lineNum, st.getPosition(), s, "Expected field domain name, got \"" + fdName + "\"");
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
                    outputError(lineNum, st.getPosition(), s, "Cannot parse field domain number \"" + number + "\"");
                    throw new IllegalArgumentException();
                }
                fdName = fdName.substring(0, numIndex);
            }
            Domain fd = getDomain(fdName);
            if (fd == null) {
                outputError(lineNum, st.getPosition(), s, "Unknown field domain " + fdName);
                throw new IllegalArgumentException();
            }
            String option;
            if (fdNum != -1) option = fdName + fdNum;
            else option = "";
            attributes.add(new Attribute(fName, fd, option));
            String comma = nextToken(st);
            if (comma.equals(")")) break;
            if (!comma.equals(",")) {
                outputError(lineNum, st.getPosition(), s, "Expected \",\" or \")\", got \"" + comma + "\"");
                throw new IllegalArgumentException();
            }
        }
        if (nameToRelation.containsKey(name)) {
            System.err.println("Error, relation " + name + " redefined on line " + lineNum + ", ignoring.");
            return null;
        }
        Relation r = createRelation(name, attributes);
        Pattern constraintPattern = Pattern.compile("(\\w+)([=<])(\\w+)");
        while (st.hasMoreTokens()) {
            String option = nextToken(st);
            Matcher constraintMatcher = constraintPattern.matcher(option);
            if (option.equals("output")) {
                relationsToDump.add(r);
            } else if (option.equals("outputtuples")) {
                relationsToDumpTuples.add(r);
            } else if (option.equals("input")) {
                relationsToLoad.add(r);
            } else if (option.equals("inputtuples")) {
                relationsToLoadTuples.add(r);
            } else if (option.equals("printtuples")) {
                relationsToPrintTuples.add(r);
            } else if (option.equals("printsize")) {
                relationsToPrintSize.add(r);
            } else if (option.equals("{")) {
                String s2 = nextToken(st);
                StringBuffer sb = new StringBuffer();
                while (!s2.equals("}")) {
                    sb.append(' ');
                    sb.append(s2);
                    if (!st.hasMoreTokens()) {
                        outputError(lineNum, st.getPosition(), s, "Expected \"}\" to terminate code block");
                        throw new IllegalArgumentException();
                    }
                    s2 = nextToken(st);
                }
                CodeFragment f = new CodeFragment(sb.toString(), r);
                r.onUpdate.add(f);
            } else if (constraintMatcher.matches()) {
                parseAndAddConstraint(r, constraintMatcher);
            } else {
                outputError(lineNum, st.getPosition(), s, "Unexpected option '" + option + "'");
                throw new IllegalArgumentException();
            }
        }
        if (!r.constraints.isEmpty()) {
            r.constraints.satisfy();
        }
        return r;
    }

    /**
     * Parse and add an attribute constraint.
     * 
     * @param r  relation to add constraint for
     * @param m  constraint pattern matcher
     */
    public void parseAndAddConstraint(Relation r, Matcher m) {
        if (m.matches()) {
            String leftAttr = m.group(1);
            String type = m.group(2);
            String rightAttr = m.group(3);
            Attribute left = null;
            Attribute right = null;
            for (Iterator it = r.getAttributes().iterator(); it.hasNext();) {
                Attribute a = (Attribute) it.next();
                if (a.attributeName.equals(leftAttr)) left = a;
                if (a.attributeName.equals(rightAttr)) right = a;
            }
            if (left == null) {
                System.out.println("Specified Attribute not found: " + leftAttr);
                throw new IllegalArgumentException();
            } else if (right == null) {
                System.out.println("Specified Attribute not found: " + rightAttr);
                throw new IllegalArgumentException();
            }
            
            if (type.equals("=")) r.constraints.addInterleavedConstraint(new InterleavedConstraint(r,left,r,right,10));
            else if (type.equals("<")) r.constraints.addBeforeConstraint(new BeforeConstraint(r,left,r,right,10));
            if (TRACE) System.out.println("parsed constraint: " + leftAttr + " " + type + " " + rightAttr);
        } else {
            //handle error
        }
    }

    /**
     * Delete the given relation.
     * 
     * @param r  relation to delete
     */
    void deleteRelation(Relation r) {
        relationsToDump.remove(r);
        relationsToDumpTuples.remove(r);
        relationsToLoad.remove(r);
        relationsToLoadTuples.remove(r);
        relationsToPrintSize.remove(r);
        relationsToPrintTuples.remove(r);
        nameToRelation.remove(r.name);
    }

    /**
     * Parse an inference rule.
     * 
     * @param lineNum  current line number for outputting error messages
     * @param s  string containing rule to parse
     * @return  new inference rule
     */
    InferenceRule parseRule(int lineNum, String s) {
        MyStringTokenizer st = new MyStringTokenizer(s, " \t(,/).=!<>", true);
        Map/* <String,Variable> */nameToVar = new HashMap();
        RuleTerm bottom = parseRuleTerm(lineNum, s, nameToVar, st);
        String sep = nextToken(st);
        List/* <RuleTerm> */terms = new LinkedList();
        if (!sep.equals(".")) {
            if (!sep.equals(":-")) {
                outputError(lineNum, st.getPosition(), s, "Expected \":-\", got \"" + sep + "\"");
                throw new IllegalArgumentException();
            }
            for (;;) {
                RuleTerm rt = parseRuleTerm(lineNum, s, nameToVar, st);
                if (rt == null) break;
                terms.add(rt);
                sep = nextToken(st);
                if (sep.equals(".")) break;
                if (!sep.equals(",")) {
                    outputError(lineNum, st.getPosition(), s, "Expected \".\" or \",\", got \"" + sep + "\"");
                    throw new IllegalArgumentException();
                }
            }
        }
        InferenceRule ir = createInferenceRule(terms, bottom);
        ir = parseRuleOptions(lineNum, s, ir, st);
        return ir;
    }

    /**
     * Parse the options for an inference rule.
     * 
     * @param lineNum  current line number for outputting error messages
     * @param s  current line for outputting error messages
     * @param ir  inference rule to parse options for
     * @param st  string tokenizer containing options to parse
     * @return  the resulting rule
     */
    InferenceRule parseRuleOptions(int lineNum, String s, InferenceRule ir, MyStringTokenizer st) {
        while (st.hasMoreTokens()) {
            String option = nextToken(st);
            if (option.equals("split")) {
                if (!SPLIT_NO_RULES) {
                    if (TRACE) out.println("Splitting rule " + ir);
                    ir.split = true;
                }
            } else if (option.equals("number")) {
                if (TRACE) out.println("Rule " + ir + " defines a numbering");
                ir = createNumberingRule(ir);
            } else if (option.equals("single")) {
                if (TRACE) out.println("Rule " + ir + " only adds a single satisfying assignment");
                ir.single = true;
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
            } else if (option.equals("pre") || option.equals("post") || option.equals("{")) {
                StringBuffer sb = new StringBuffer();
                String s2 = nextToken(st);
                int type = 2;
                if (!option.equals("{")) {
                    if (option.equals("pre")) type = 1;
                    if (!s2.equals("{")) {
                        outputError(lineNum, st.getPosition(), s, "Expected \"{\", but found \""+s2+"\"");
                        throw new IllegalArgumentException();
                    }
                    s2 = nextToken(st);
                }
                while (!s2.equals("}")) {
                    sb.append(' ');
                    sb.append(s2);
                    if (!st.hasMoreTokens()) {
                        outputError(lineNum, st.getPosition(), s, "Expected \"}\" to terminate code block");
                        throw new IllegalArgumentException();
                    }
                    s2 = nextToken(st);
                }
                CodeFragment f = new CodeFragment(sb.toString(), ir);
                if (type == 1) ir.preCode.add(f);
                else ir.postCode.add(f);
            } else if (option.equals("modifies")) {
                String relationName = nextToken(st);
                if (relationName.equals("(")) {
                    for (;;) {
                        relationName = nextToken(st);
                        if (relationName.equals(",")) continue;
                        if (relationName.equals(")")) break;
                        Relation r = getRelation(relationName);
                        if (r == null) {
                            outputError(lineNum, st.getPosition(), s, "Unknown relation \""+relationName+"\"");
                            throw new IllegalArgumentException();
                        }
                        ir.extraDefines.add(r);
                    }
                } else {
                    Relation r = getRelation(relationName);
                    if (r == null) {
                        outputError(lineNum, st.getPosition(), s, "Unknown relation \""+relationName+"\"");
                        throw new IllegalArgumentException();
                    }
                    ir.extraDefines.add(r);
                }
            } else {
                // todo: pri=#, maxiter=#
                outputError(lineNum, st.getPosition(), s, "Unknown rule option \"" + option + "\"");
                throw new IllegalArgumentException();
            }
        }
        if (hasDuplicateVars && !(ir instanceof NumberingRule)) {
            outputError(lineNum, st.getPosition(), s, "Variable repeated multiple times in a single term");
            throw new IllegalArgumentException();
        }
        hasDuplicateVars = false;
        return ir;
    }

    /**
     * Flag that is set if a rule term has repeated variables.
     */
    boolean hasDuplicateVars;
    /**
     * Parse a term of an inference rule.
     * 
     * @param lineNum  current line number for outputting error messages
     * @param s  current line for outputting error messages
     * @param nameToVar  map from variable names to variables
     * @param st  string tokenizer containing rule term to parse
     * @return  rule term, or null if string is "?"
     */
    RuleTerm parseRuleTerm(int lineNum, String s, Map/*<String,Variable>*/ nameToVar, MyStringTokenizer st) {
        boolean negated = false;
        String relationName = nextToken(st);
        if (relationName.equals("?")) {
            return null;
        }
        if (relationName.equals("!")) {
            negated = true;
            relationName = nextToken(st);
        }
        String openParen = nextToken(st);
        boolean flip = false;
        boolean less = false;
        boolean greater = false;
        if (openParen.equals("!")) {
            flip = true;
            openParen = nextToken(st);
        } else if (openParen.equals("<")) {
            less = true;
            openParen = nextToken(st);
        } else if (openParen.equals(">")) {
            greater = true;
            openParen = nextToken(st);
        }
        if (openParen.equals("=") || less || greater) {
            if (negated) {
                outputError(lineNum, st.getPosition(), s, "Unexpected \"!\"");
                throw new IllegalArgumentException();
            }
            // "a = b".
            boolean equals = openParen.equals("=");
            String varName1 = relationName;
            String varName2 = equals ? nextToken(st) : openParen;
            Variable var1, var2;
            var1 = (Variable) nameToVar.get(varName1);
            Relation r;
            if (equals && varName2.equals(">")) {
                if (negated || less || greater) {
                    outputError(lineNum, st.getPosition(), s, "Unexpected \"!\", \"<\", or \">\" with \"=>\"");
                    throw new IllegalArgumentException();
                }
                // "a => b".
                varName2 = nextToken(st);
                var2 = (Variable) nameToVar.get(varName2);
                if (var1 == null || var2 == null) {
                    outputError(lineNum, st.getPosition(), s, "Cannot use \"=>\" on unbound variables.");
                    throw new IllegalArgumentException();
                }
                r = getMapRelation(var1.domain, var2.domain);
            } else {
                var2 = (Variable) nameToVar.get(varName2);
                if (var1 == null) {
                    if (var2 == null) {
                        outputError(lineNum, st.getPosition(), s, "Cannot use \"=\", \"!=\", \"<\", \"<=\", \">\", \">=\", on two unbound variables.");
                        throw new IllegalArgumentException();
                    }
                    var1 = parseVariable(var2.domain, nameToVar, varName1);
                } else {
                    if (var2 == null) {
                        var2 = parseVariable(var1.domain, nameToVar, varName2);
                    }
                }
                if (less) {
                    r = equals ? getLessThanOrEqualRelation(var1.domain, var2.domain) : getLessThanRelation(var1.domain, var2.domain);
                } else if (greater) {
                    r = equals ? getGreaterThanOrEqualRelation(var1.domain, var2.domain) : getGreaterThanRelation(var1.domain, var2.domain);
                } else {
                    r = flip ? getNotEquivalenceRelation(var1.domain, var2.domain) : getEquivalenceRelation(var1.domain, var2.domain);
                }
            }
            List vars = new Pair(var1, var2);
            RuleTerm rt = new RuleTerm(r, vars);
            return rt;
        } else if (!openParen.equals("(")) {
            outputError(lineNum, st.getPosition(), s, "Expected \"(\" or \"=\", got \"" + openParen + "\"");
            throw new IllegalArgumentException();
        }
        if (flip) {
            outputError(lineNum, st.getPosition(), s, "Unexpected \"!\"");
            throw new IllegalArgumentException();
        }
        Relation r = getRelation(relationName);
        if (r == null) {
            outputError(lineNum, st.getPosition(), s, "Unknown relation " + relationName);
            throw new IllegalArgumentException();
        }
        if (negated) r = r.makeNegated(this);
        List/*<Variable>*/ vars = new LinkedList();
        for (;;) {
            if (r.attributes.size() <= vars.size()) {
                outputError(lineNum, st.getPosition(), s, "Too many fields for " + r);
                throw new IllegalArgumentException();
            }
            Attribute a = (Attribute) r.attributes.get(vars.size());
            Domain fd = a.attributeDomain;
            String varName = nextToken(st);
            Variable var = parseVariable(fd, nameToVar, varName);
            if (vars.contains(var)) {
                hasDuplicateVars = true;
            }
            vars.add(var);
            if (var.domain == null) var.domain = fd;
            else if (var.domain != fd) {
                outputError(lineNum, st.getPosition(), s, "Variable " + var + " used as both " + var.domain + " and " + fd);
                throw new IllegalArgumentException();
            }
            String sep = nextToken(st);
            if (sep.equals(")")) break;
            if (!sep.equals(",")) {
                outputError(lineNum, st.getPosition(), s, "Expected ',' or ')', got '" + sep + "'");
                throw new IllegalArgumentException();
            }
        }
        if (r.attributes.size() != vars.size()) {
            outputError(lineNum, st.getPosition(), s, "Wrong number of vars in rule term for " + relationName);
            throw new IllegalArgumentException();
        }
        RuleTerm rt = new RuleTerm(r, vars);
        return rt;
    }


    /**
     * Parse a variable or a constant.
     * 
     * @param fd  domain of variable/constant
     * @param nameToVar  map from names to variables for this rule
     * @param varName  name of variable/constant
     * @return  variable/constant
     */
    Variable parseVariable(Domain fd, Map nameToVar, String varName) {
        char firstChar = varName.charAt(0);
        Variable var;
        if (firstChar >= '0' && firstChar <= '9') {
            var = new Constant(Long.parseLong(varName));
        } else if (firstChar == '"') {
            String namedConstant = varName.substring(1, varName.length() - 1);
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

    boolean includeRelationInComeFromQuery(Relation r, boolean includeDerivations) {
        String comeFromIncludes = System.getProperty("comeFromRelations");
        if (comeFromIncludes == null) return true;
        String[] names = comeFromIncludes.split(":");
        boolean include = false;
        for (int i=0; !include && i<names.length; i++) {
            if (includeDerivations) {
                if (r.name.startsWith(names[i])) include = true;
            }
            else {
                if (r.name.equals(names[i])) include = true;
            }
        }
        return include;
    }

    /**
     * Compute a come-from query.  A come-from query includes both :- and ?.
     * 
     * @param rt initial rule term
     * @return  list of inference rules implementing the come-from query
     */
    List/*<InferenceRule>*/ comeFromQuery(RuleTerm rt, List extras, boolean single) {
        List newRules = new LinkedList();
        
        boolean oldTRACE = TRACE;
        TRACE = TRACE || (System.getProperty("traceComeFromQuery") != null);

        Relation r = rt.relation;
        Relation r2 = createRelation(r.name+"_q", r.attributes);
        
        RuleTerm my_rt = new RuleTerm(r2, rt.variables);
        InferenceRule my_ir = createInferenceRule(Collections.singletonList(rt), my_rt);
        //my_ir.single = single;
        if (TRACE) out.println("Adding rule: "+my_ir);
        newRules.add(my_ir);
        
        DependenceNavigator nav = new DependenceNavigator(rules);
        Map/*<Relation,Relation>*/ toQueryRelation = new LinkedHashMap();
        LinkedList worklist = new LinkedList();
        toQueryRelation.put(r, r2);
        worklist.add(r);
        while (!worklist.isEmpty()) {
            // r: the relation we want to query.
            r = (Relation) worklist.removeFirst();
            // r2: the tuples in the relation that contribute to the answer.
            r2 = (Relation) toQueryRelation.get(r);
            if (TRACE) out.println("Finding contributions in relation "+r+": "+r2);
            
            // Visit each rule that can add tuples to "r".
            Collection rules = nav.prev(r);
            for (Iterator i = rules.iterator(); i.hasNext(); ) {
                InferenceRule ir = (InferenceRule) i.next();
                if (TRACE) out.println("This rule can contribute: "+ir);
                Assert._assert(ir.bottom.relation == r);
                
                // Build up a new query that consists of "r2" and all of the subgoals.
                List/*<RuleTerm>*/ terms = new LinkedList();
                Map varMap = new LinkedHashMap();
                RuleTerm rt2 = new RuleTerm(r2, ir.bottom.variables);
                terms.add(rt2);
                addToVarMap(varMap, rt2);
                for (Iterator j = ir.top.iterator(); j.hasNext(); ) {
                    RuleTerm rt3 = (RuleTerm) j.next();
                    terms.add(rt3);
                    addToVarMap(varMap, rt3);
                    Relation r3 = rt3.relation;
                    Relation r4 = (Relation) toQueryRelation.get(r3);
                    if (r4 == null) {
                        boolean relevantRelation = includeRelationInComeFromQuery(r3,true);
                        //relevantRelation = true;
                        if (!relevantRelation) {
                            if (TRACE) out.println("Skipping contribution relation "+r3);
                        }
                        else {
                        // New relation, visit it.
                        worklist.add(r3);
                        r4 = createRelation(r3.name+"_q", r3.attributes);
                        toQueryRelation.put(r3, r4);
                        if (TRACE) out.println("Adding contribution relation "+r3+": "+r4);
                        }
                    }
                }
                List vars = new ArrayList(varMap.keySet());
                List attributes = new ArrayList(vars.size());
                for (Iterator k = varMap.entrySet().iterator(); k.hasNext(); ) {
                    Map.Entry e = (Map.Entry) k.next();
                    Variable v = (Variable) e.getKey();
                    String name = (String) e.getValue();
                    attributes.add(new Attribute(name, v.getDomain(), ""));
                }
                Relation bottomr = createRelation(r.name+"_q"+ir.id, attributes);
                RuleTerm bottom = new RuleTerm(bottomr, vars);
                InferenceRule newrule = createInferenceRule(terms, bottom);
                newrule.single = single;
                if (TRACE) out.println("Adding rule: "+newrule);
                newRules.add(newrule);
                
                // Now bottomr contains assignments to all of the variables.

                // Make a printable relation of bottomr, without the contexts:
                if(includeRelationInComeFromQuery(r,false)) {
                    List vars_noC = new ArrayList(varMap.keySet());
                    List attributes_noC = new ArrayList(vars.size());
                    for (Iterator k = varMap.entrySet().iterator(); k.hasNext(); ) {
                        Map.Entry e = (Map.Entry) k.next();
                        Variable v = (Variable) e.getKey();
                        String name = (String) e.getValue();
                        if (!name.startsWith("c")) {
                            attributes_noC.add(new Attribute(name, v.getDomain(), ""));
                        }
                        else {
                            vars_noC.remove(v);
                            if (TRACE) out.println("Excluding from non-context version: "+name);
                        }
                    }
                    Relation bottomr_noC = createRelation(r.name+"_q"+ir.id+"_noC", attributes_noC);
                    RuleTerm bottom_noC = new RuleTerm(bottomr_noC, vars_noC);
                    InferenceRule newrule_noC = createInferenceRule(Collections.singletonList(bottom), bottom_noC);
                    newrule_noC.single = single;
                    if (TRACE) out.println("Adding rule: "+newrule_noC);
                    newRules.add(newrule_noC);
                    relationsToPrintTuples.add(bottomr_noC);
                    relationsToDump.add(bottomr_noC);
                }
                
                // For each subgoal, build a new rule that adds to the contribute relations
                // for that subgoal.
                List terms2 = Collections.singletonList(bottom);
                for (Iterator j = ir.top.iterator(); j.hasNext(); ) {
                    RuleTerm rt3 = (RuleTerm) j.next();
                    Relation r3 = rt3.relation;
                    Relation r4 = (Relation) toQueryRelation.get(r3);
                    if (r4 != null) {
                    Assert._assert(r4 != null, "no mapping for "+r3);
                    RuleTerm rt4 = new RuleTerm(r4, rt3.variables);
                    InferenceRule newrule2 = createInferenceRule(terms2, rt4);
                    //newrule2.single = single;
                    if (TRACE) out.println("Adding rule: "+newrule2);
                    newRules.add(newrule2);
                    }
                }
            }
        }
        
        for (Iterator i = toQueryRelation.values().iterator(); i.hasNext(); ) {
            Relation r4 = (Relation) i.next();
            relationsToPrintTuples.add(r4);
        }

        TRACE = oldTRACE;
        
        return newRules;
    }
    
    /**
     * Utility function to add the variables in the given rule term to the given
     * variable map from Variables to Strings.  This is used in constructing
     * come-from queries.
     * 
     * @param varMap  variable map
     * @param rt  rule term whose variables we want to add
     */
    private void addToVarMap(Map/*<Variable,String>*/ varMap, RuleTerm rt) {
        for (Iterator i = rt.variables.iterator(); i.hasNext(); ) {
            Variable v = (Variable) i.next();
            if (v.name.equals("_")) continue;
            String name;
            if (v instanceof Constant) {
                name = rt.relation.getAttribute(rt.variables.indexOf(v)).attributeName;
            } else {
                name = v.toString();
            }
            varMap.put(v, name);
        }
    }
    
    /**
     * Parse a query.  A query is a statement that ends with '?'.
     * 
     * @param lineNum  current line number, for outputting error messages
     * @param s  line to parse
     * @return  list of inference rules implementing the query.
     */
    List/*<InferenceRule>*/ parseQuery(int lineNum, String s) {
        MyStringTokenizer st = new MyStringTokenizer(s, " \t(,/).=~!?<>", true);
        Map/*<String,Variable>*/ nameToVar = new HashMap();
        
        if (s.indexOf(":-") > 0) {
            RuleTerm rt = parseRuleTerm(lineNum, s, nameToVar, st);
            String sep = nextToken(st);
            if (!sep.equals(":-")) {
                outputError(lineNum, st.getPosition(), s, "Expected \":-\", got \"" + sep + "\"");
                throw new IllegalArgumentException();
            }
            List/*<RuleTerm>*/ extras = new LinkedList();
            for (;;) {
                RuleTerm rt2 = parseRuleTerm(lineNum, s, nameToVar, st);
                if (rt2 == null) break;
                extras.add(rt2);
                String sep2 = nextToken(st);
                if (sep2.equals("?")) break;
                if (!sep2.equals(",")) {
                    outputError(lineNum, st.getPosition(), s, "Expected \",\", got \"" + sep2 + "\"");
                    throw new IllegalArgumentException();
                }
            }
            boolean single = false;
            while (st.hasMoreTokens()) {
                String option = nextToken(st);
                if (option.equals("single")) {
                    single = true;
                } else {
                    outputError(lineNum, st.getPosition(), s, "Unknown query option \"" + option + "\"");
                    throw new IllegalArgumentException();
                }
            }
            return comeFromQuery(rt, extras, single);
        }
        List/*<RuleTerm>*/ terms = new LinkedList();
        Map varMap = new LinkedHashMap();
        for (;;) {
            RuleTerm rt = parseRuleTerm(lineNum, s, nameToVar, st);
            if (rt == null) break;
            terms.add(rt);
            for (Iterator i = rt.variables.iterator(); i.hasNext(); ) {
                Variable v = (Variable) i.next();
                if (v.name.equals("_")) continue;
                String name;
                if (v instanceof Constant) {
                    name = rt.relation.getAttribute(rt.variables.indexOf(v)).attributeName;
                } else {
                    name = v.toString();
                }
                varMap.put(v, name);
            }
            String sep = nextToken(st);
            if (sep.equals("?")) break;
            if (!sep.equals(",")) {
                outputError(lineNum, st.getPosition(), s, "Expected \",\", got \"" + sep + "\"");
                throw new IllegalArgumentException();
            }
        }
        List vars = new ArrayList(varMap.keySet());
        List attributes = new ArrayList(vars.size());
        for (Iterator i = varMap.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry) i.next();
            Variable v = (Variable) e.getKey();
            String name = (String) e.getValue();
            attributes.add(new Attribute(name, v.getDomain(), ""));
        }
        Relation r = createRelation("query@"+lineNum, attributes);
        RuleTerm bottom = new RuleTerm(r, vars);
        InferenceRule ir = createInferenceRule(terms, bottom);
        ir = parseRuleOptions(lineNum, s, ir, st);
        relationsToPrintTuples.add(r);
        return Collections.singletonList(ir);
    }
    
    /**
     * Get the equivalence relation for the given domains.
     * 
     * @param fd1  first domain
     * @param fd2  second domain
     * @return  equivalence relation on those domains
     */
    Relation getEquivalenceRelation(Domain fd1, Domain fd2) {
        if (fd1.name.compareTo(fd2.name) > 0) return getEquivalenceRelation(fd2, fd1);
        Object key = new Pair(fd1, fd2);
        Collection c = equivalenceRelations.getValues(key);
        Relation r;
        if (c.isEmpty()) {
            equivalenceRelations.put(key, r = createEquivalenceRelation(fd1, fd2));
        } else {
            r = (Relation) c.iterator().next();
        }
        return r;
    }

    /**
     * Get the negated equivalence relation for the given domains.
     * 
     * @param fd1  first domain
     * @param fd2  second domain
     * @return  negated equivalence relation on those domains
     */
    Relation getNotEquivalenceRelation(Domain fd1, Domain fd2) {
        Relation r = getEquivalenceRelation(fd1, fd2);
        return r.makeNegated(this);
    }
    
    /**
     * Get the greater-than-or-equal-to relation for the given domains.
     * 
     * @param fd1  first domain
     * @param fd2  second domain
     * @return  greater-than-or-equal-to relation on those domains
     */
    Relation getGreaterThanOrEqualRelation(Domain fd1, Domain fd2) {
        Relation r = getLessThanRelation(fd1, fd2);
        return r.makeNegated(this);
    }

    /**
     * Get the greater-than relation for the given domains.
     * 
     * @param fd1  first domain
     * @param fd2  second domain
     * @return  greater-than relation on those domains
     */
    Relation getGreaterThanRelation(Domain fd1, Domain fd2) {
        Object key = new Pair(fd1, fd2);
        Collection c = greaterThanRelations.getValues(key);
        Relation r;
        if (c.isEmpty()) {
            greaterThanRelations.put(key, r = createGreaterThanRelation(fd1, fd2));
        } else {
            r = (Relation) c.iterator().next();
        }
        return r;
    }

    /**
     * Get the greater-than relation for the given domains.
     * 
     * @param fd1  first domain
     * @param fd2  second domain
     * @return  less-than relation on those domains
     */
    Relation getLessThanRelation(Domain fd1, Domain fd2) {
        Object key = new Pair(fd1, fd2);
        Collection c = lessThanRelations.getValues(key);
        Relation r;
        if (c.isEmpty()) {
            lessThanRelations.put(key, r = createLessThanRelation(fd1, fd2));
        } else {
            r = (Relation) c.iterator().next();
        }
        return r;
    }

    /**
     * Get the less-than-or-equal-to relation for the given domains.
     * 
     * @param fd1  first domain
     * @param fd2  second domain
     * @return  less-than-or-equal-to relation on those domains
     */
    Relation getLessThanOrEqualRelation(Domain fd1, Domain fd2) {
        Relation r = getGreaterThanRelation(fd1, fd2);
        return r.makeNegated(this);
    }

    /**
     * Get the map relation for the given domains.
     * 
     * @param fd1  first domain
     * @param fd2  second domain
     * @return  map relation on those domains
     */
    Relation getMapRelation(Domain fd1, Domain fd2) {
        Object key = new Pair(fd1, fd2);
        Relation r = (Relation) mapRelations.get(key);
        if (r == null) {
            mapRelations.put(key, r = createMapRelation(fd1, fd2));
        }
        return r;
    }
    
    /**
     * Load in the initial relations.
     * 
     * @throws IOException
     */
    void loadInitialRelations() throws IOException {
        if (USE_IR) return;
        for (Iterator i = relationsToLoad.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            try {
                r.load();
            } catch (IOException x) {
                System.out.println("WARNING: Cannot load bdd " + r + ": " + x.toString());
            }
        }
        for (Iterator i = relationsToLoadTuples.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            try {
                r.loadTuples();
            } catch (IOException x) {
                System.out.println("WARNING: Cannot load tuples " + r + ": " + x.toString());
            }
        }
    }

    /**
     * Split inference rules.
     */
    void splitRules() {
        List newRules = new LinkedList();
        for (Iterator i = rules.iterator(); i.hasNext();) {
            InferenceRule r = (InferenceRule) i.next();
            if (!SPLIT_NO_RULES && (SPLIT_ALL_RULES || r.split)) newRules.addAll(r.split(rules.indexOf(r)));
        }
        rules.addAll(newRules);
    }

class RuleSorter implements Comparator {
        long getRuleTime(Object rule) {
            if (rule instanceof BDDInferenceRule) {
                return ((BDDInferenceRule)rule).totalTime;
            }
            else if (rule instanceof NumberingRule) {
                return ((NumberingRule)rule).totalTime;
            }
            else {
                return 0;
            }
        }

        public int compare(Object o1, Object o2) {
            return (int)(getRuleTime(o1) - getRuleTime(o2));
        }
    }

    /**
     * Report rule statistics.
     */
    void reportStats() {
        if(USE_IR) return;
        List sortedRules = new LinkedList(rules);
        Collections.sort(sortedRules,new RuleSorter());
        //        List fbsList = new LinkedList();
        for (Iterator i = sortedRules.iterator(); i.hasNext();) {
            InferenceRule r = (InferenceRule) i.next();
            r.reportStats();
            /*
            if (r instanceof BDDInferenceRule) {
                BDDInferenceRule bddir = (BDDInferenceRule) r;
                if (bddir.fbs != null) fbsList.add(bddir.fbs);
            }
        }
        for (Iterator i = fbsList.iterator(); i.hasNext();) {
            ((FindBestSplit)i.next()).reportStats();
            */
        }
    }

    /**
     * Save the results and print sizes.
     * 
     * @throws IOException
     */
    void saveResults() throws IOException {
       if (USE_IR) return;
        for (Iterator i = relationsToPrintSize.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            double size = r.dsize();
            DecimalFormat myFormatter = new DecimalFormat("0.");
            String output = myFormatter.format(size);
            out.println("SIZE OF " + r + ": " + output);
        }
        for (Iterator i = relationsToPrintTuples.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            double size = r.dsize();
            DecimalFormat myFormatter = new DecimalFormat("0.");
            String output = myFormatter.format(size);
            out.println("Tuples in "+r+": ("+output+")");
            final int MAX = 100;
            int num = MAX;
            TupleIterator j = r.iterator();
            while (j.hasNext()) {
                if (--num < 0) break;
                BigInteger[] a = j.nextTuple();
                out.print("\t(");
                for (int k = 0; k < a.length; ++k) {
                    if (k > 0) out.print(',');
                    Attribute at = r.getAttribute(k);
                    out.print(at);
                    out.print('=');
                    out.print(at.attributeDomain.toString(a[k]));
                    if (at.attributeDomain.map != null &&
                        a[k].signum() >= 0 && a[k].intValue() < at.attributeDomain.map.size()) {
                        out.print('(');
                        out.print(a[k]);
                        out.print(')');
                    }
                }
                out.println(")");
            }
            if (j.hasNext()) {
                out.println("\tand more ("+r.size()+" in total).");
            }
        }
        for (Iterator i = relationsToDump.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping BDD for " + r);
            r.save();
        }
        for (Iterator i = relationsToDumpTuples.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping tuples for " + r);
            r.saveTuples();
        }
        for (Iterator i = dotGraphsToDump.iterator(); i.hasNext();) {
            Dot dot = (Dot) i.next();
            if (NOISY) out.println("Dumping dot graph");
            dot.outputGraph();
        }
    }

    /**
     * Return the number of relations.
     * 
     * @return the number of relations
     */
    public int getNumberOfRelations() {
        return relations.size();
    }

    /**
     * Return the list of rules.
     * 
     * @return the list of rules
     */
    public List getRules() {
        return rules;
    }

    /**
     * Returns the ith rule.
     * 
     * @param i  index
     * @return  inference rule
     */
    public InferenceRule getRule(int i) {
        InferenceRule ir = (InferenceRule) rules.get(i);
        if (ir.id == i) return ir;
        System.out.println("Id "+i+" doesn't match id "+ir.id+": "+ir);
        for (Iterator j = rules.iterator(); j.hasNext(); ) {
            ir = (InferenceRule) j.next();
            if (ir.id == i) return ir;
        }
        return null;
    }
    
    /**
     * Returns the inference rule with the given name.
     * 
     * @param s  rule name
     * @return  inference rul
     */
    public InferenceRule getRule(String s) {
        if (!s.startsWith("rule")) return null;
        int index = Integer.parseInt(s.substring(4));
        return getRule(index);
    }
    
    public InferenceRule getRuleThatContains(Variable v) {
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            InferenceRule ir = (InferenceRule) i.next();
            if (ir.necessaryVariables == null) continue; // NumberingRule (?)
            if (ir.necessaryVariables.contains(v) ||
                ir.unnecessaryVariables.contains(v)) return ir;
        }
        return null;
    }
    
    /**
     * Return the iteration flow graph.  This contains the iteration order.
     * 
     * @return  iteration flow graph
     */
    public IterationFlowGraph getIterationFlowGraph() {
        return ifg;
    }
    
    /**
     * Return the collection of relations to load.
     * 
     * @return  the collection of relations to load.
     */
    public Collection getRelationsToLoad() {
        return relationsToLoad;
    }

    /**
     * Return the collection of relations to save.
     * 
     * @return  the collection of relations to save.
     */
    public Collection getRelationsToSave() {
        return relationsToDump;
    }
    
    /**
     * Replacement main() function that checks if we have the BDD library in the
     * classpath.
     * 
     * @param args
     * @throws IOException
     */
    public static void main(String[] args) throws IOException, InstantiationException, IllegalAccessException, ClassNotFoundException {
        // Make sure we have the BDD library in our classpath.
        try {
            Class.forName("net.sf.javabdd.BDD");
        } catch (ClassNotFoundException x) {
            ClassLoader cl = addBDDLibraryToClasspath(args);
            // Reflective invocation under the new class loader.
            Reflect.invoke(cl, Solver.class.getName(), "main2", new Class[] {String[].class}, new Object[] {args});
            return;
        }
        // Just call it directly.
        main2(args);
    }
    
    public static ClassLoader addBDDLibraryToClasspath(String[] args) throws IOException {
        System.out.print("BDD library is not in classpath!  ");
        URL url;
        url = HijackingClassLoader.getFileURL("javabdd.jar");
        if (url == null) {
            String sep = System.getProperty("file.separator");
            url = HijackingClassLoader.getFileURL(".."+sep+"JavaBDD");
        }
        if (url == null) {
            System.err.println("Cannot find JavaBDD library!");
            System.exit(-1);
            return null;
        }
        System.out.println("Adding "+url+" to classpath.");
        URL url2 = new File(".").toURL();
        return new HijackingClassLoader(new URL[] {url, url2});
    }
    
}
