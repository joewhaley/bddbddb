// Solver.java, created Mar 16, 2004 7:07:16 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.ArrayList;
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
import java.text.DecimalFormat;
import org.sf.bddbddb.InferenceRule.DependenceNavigator;
import org.sf.bddbddb.dataflow.PartialOrder.Constraint;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.IndexMap;
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
    
    /** Trace output stream. */
    PrintStream out = System.out;
    
    /** Base directory where to load/save files. */
    String basedir = System.getProperty("basedir");
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
    Map/*<Domain,Relation>*/ equivalenceRelations;
    /** List of inference rules. */
    List/*<InferenceRule>*/ rules;
    
    /** Flag that is set on initialization. */
    boolean isInitialized;
    
    Collection/*<Relation>*/ relationsToLoad;
    Collection/*<Relation>*/ relationsToLoadTuples;
    Collection/*<Relation>*/ relationsToDump;
    Collection/*<Relation>*/ relationsToDumpNegated;
    Collection/*<Relation>*/ relationsToDumpTuples;
    Collection/*<Relation>*/ relationsToDumpNegatedTuples;
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
     * @param fd  domain of relation
     * @return  new equivalence relation
     */
    abstract Relation createEquivalenceRelation(Domain fd);

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
        equivalenceRelations = new HashMap();
        rules = new LinkedList();
        relationsToLoad = new LinkedList();
        relationsToLoadTuples = new LinkedList();
        relationsToDump = new LinkedList();
        relationsToDumpNegated = new LinkedList();
        relationsToDumpTuples = new LinkedList();
        relationsToDumpNegatedTuples = new LinkedList();
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

    /**
     * Get all the equivalence relations.
     * 
     * @return  collection of equivalence relations
     */
    public Collection getEquivalenceRelations() {
        return equivalenceRelations.values();
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
    
    /**
     * The entry point to the application.
     * 
     * @param args  command line arguments
     * @throws IOException
     * @throws InstantiationException
     * @throws IllegalAccessException
     * @throws ClassNotFoundException
     */
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
        if (dis.NOISY) dis.out.println("Opening Datalog program \"" + inputFilename + "\"");
        MyReader in = new MyReader(new LineNumberReader(new FileReader(inputFilename)));
        dis.initializeBasedir(inputFilename);
        dis.readDatalogProgram(in);
        if (dis.NOISY) dis.out.println(dis.nameToDomain.size() + " field domains.");
        if (dis.NOISY) dis.out.println(dis.nameToRelation.size() + " relations.");
        if (dis.NOISY) dis.out.println(dis.rules.size() + " rules.");
        in.close();
        if (dis.NOISY) dis.out.print("Splitting rules: ");
        dis.splitRules();
        if (dis.NOISY) dis.out.println("done.");
        if (dis.NOISY) dis.out.print("Initializing solver: ");
        dis.initialize();
        if (dis.NOISY) dis.out.println("done.");
        if (dis.NOISY) dis.out.print("Loading initial relations: ");
        long time = System.currentTimeMillis();
        dis.loadInitialRelations();
        time = System.currentTimeMillis() - time;
        if (dis.NOISY) dis.out.println("done. (" + time + " ms)");
        dis.out.println("Solving: ");
        time = System.currentTimeMillis();
        dis.solve();
        time = System.currentTimeMillis() - time;
        dis.out.println("done. (" + time + " ms)");
        long solveTime = time;
        dis.finish();
        if (dis.REPORT_STATS) {
            System.out.println("SOLVE_TIME=" + solveTime);
            dis.reportStats();
        }
        if (dis.NOISY) dis.out.print("Saving results: ");
        time = System.currentTimeMillis();
        dis.saveResults();
        time = System.currentTimeMillis() - time;
        if (dis.NOISY) dis.out.println("done. (" + time + " ms)");
        dis.cleanup();
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
        if (s.indexOf(".") > 0) {
            // rule
            InferenceRule ir = parseRule(lineNum, s);
            if (TRACE) out.println("Parsed rule " + ir);
            rules.add(ir);
            return Collections.singletonList(ir);
        } else if (s.indexOf("?") > 0) {
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
                int n = Integer.parseInt(s.substring(index).trim());
                ((BDDSolver) this).BDDMINFREE = n;
            }
        } else if (s.startsWith(".findbestorder")) {
            int index = ".findbestorder".length() + 1;
            String val = "";
            if (s.length() > index) val = s.substring(index).trim();
            System.setProperty("findbestorder", val);
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
        if (name.indexOf('!') >= 0) {
            outputError(lineNum, st.getPosition(), s, "Relation name cannot contain '!'");
            throw new IllegalArgumentException();
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
            } else if (option.equals("printtuples")) {
                relationsToPrintTuples.add(r);
            } else if (option.equals("printsize")) {
                relationsToPrintSize.add(r);
            } else if (constraintMatcher.matches()) {
                parseAndAddConstraint(r, constraintMatcher);
            } else {
                outputError(lineNum, st.getPosition(), s, "Unexpected option '" + option + "'");
                throw new IllegalArgumentException();
            }
        }
        r.constraints.satisfy();
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
            Constraint c = new Constraint(left, right, 10);
            if (type.equals("=")) r.constraints.addInterleavedConstraint(c);
            else if (type.equals("<")) r.constraints.addBeforeConstraint(c);
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
        relationsToDumpNegated.remove(r);
        relationsToDumpTuples.remove(r);
        relationsToDumpNegatedTuples.remove(r);
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
        MyStringTokenizer st = new MyStringTokenizer(s, " \t(,/).=!", true);
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
            if (option.equals("split") && !SPLIT_NO_RULES) {
                if (TRACE) out.println("Splitting rule " + ir);
                ir.split = true;
            } else if (option.equals("number")) {
                if (TRACE) out.println("Rule " + ir + " defines a numbering");
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
                outputError(lineNum, st.getPosition(), s, "Unknown rule option \"" + option + "\"");
                throw new IllegalArgumentException();
            }
        }
        return ir;
    }

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
        if (openParen.equals("!")) {
            flip = true;
            openParen = nextToken(st);
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
                outputError(lineNum, st.getPosition(), s, "Variable " + var1 + " and " + var2 + " have different field domains.");
                throw new IllegalArgumentException();
            }
            Relation r = flip ? getNotEquivalenceRelation(fd) : getEquivalenceRelation(fd);
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
        List/* <Variable> */vars = new LinkedList();
        for (;;) {
            if (r.attributes.size() <= vars.size()) {
                outputError(lineNum, st.getPosition(), s, "Too many fields for " + r);
                throw new IllegalArgumentException();
            }
            Attribute a = (Attribute) r.attributes.get(vars.size());
            Domain fd = a.attributeDomain;
            String varName = nextToken(st);
            Variable var = parseVariable(fd, nameToVar, varName);
            if (false && vars.contains(var)) { // temporarily disabled to handle "number" rules.
                outputError(lineNum, st.getPosition(), s, "Duplicate variable " + var);
                throw new IllegalArgumentException();
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

    /**
     * Compute a come-from query.  A come-from query includes both :- and ?.
     * 
     * @param rt initial rule term
     * @return  list of inference rules implementing the come-from query
     */
    List/*<InferenceRule>*/ comeFromQuery(RuleTerm rt, List extras) {
        List newRules = new LinkedList();
        
        Relation r = rt.relation;
        Relation r2 = createRelation(r.name+"_q", r.attributes);
        
        RuleTerm my_rt = new RuleTerm(r2, rt.variables);
        InferenceRule my_ir = createInferenceRule(Collections.singletonList(rt), my_rt);
        if (TRACE) out.println("Adding rule: "+my_ir);
        newRules.add(my_ir);
        
        DependenceNavigator nav = new DependenceNavigator(rules);
        Map/*<Relation,Relation>*/ toQueryRelation = new HashMap();
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
                        // New relation, visit it.
                        worklist.add(r3);
                        r4 = createRelation(r3.name+"_q", r3.attributes);
                        toQueryRelation.put(r3, r4);
                        if (TRACE) out.println("Adding contribution relation "+r3+": "+r4);
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
                if (TRACE) out.println("Adding rule: "+newrule);
                newRules.add(newrule);
                
                // Now bottomr contains assignments to all of the variables.
                
                // For each subgoal, build a new rule that adds to the contribute relations
                // for that subgoal.
                List terms2 = Collections.singletonList(bottom);
                for (Iterator j = ir.top.iterator(); j.hasNext(); ) {
                    RuleTerm rt3 = (RuleTerm) j.next();
                    Relation r3 = rt3.relation;
                    Relation r4 = (Relation) toQueryRelation.get(r3);
                    Assert._assert(r4 != null, "no mapping for "+r3);
                    RuleTerm rt4 = new RuleTerm(r4, rt3.variables);
                    InferenceRule newrule2 = createInferenceRule(terms2, rt4);
                    if (TRACE) out.println("Adding rule: "+newrule2);
                    newRules.add(newrule2);
                }
            }
        }
        
        for (Iterator i = toQueryRelation.values().iterator(); i.hasNext(); ) {
            Relation r4 = (Relation) i.next();
            relationsToPrintTuples.add(r4);
        }
        
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
        MyStringTokenizer st = new MyStringTokenizer(s, " \t(,/).=!?", true);
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
            return comeFromQuery(rt, extras);
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
     * Get the equivalence relation for the given domain.
     * 
     * @param fd  domain
     * @return  equivalence relation on that domain
     */
    Relation getEquivalenceRelation(Domain fd) {
        Relation r = (Relation) equivalenceRelations.get(fd);
        if (r == null) {
            equivalenceRelations.put(fd, r = createEquivalenceRelation(fd));
        }
        return r;
    }

    /**
     * Get the negated equivalence relation for the given domain.
     * 
     * @param fd  domain
     * @return  negated equivalence relation on that domain
     */
    Relation getNotEquivalenceRelation(Domain fd) {
        Relation r = getEquivalenceRelation(fd);
        return r.makeNegated(this);
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

    /**
     * Report rule statistics.
     */
    void reportStats() {
        for (Iterator i = rules.iterator(); i.hasNext();) {
            InferenceRule r = (InferenceRule) i.next();
            r.reportStats();
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
            out.println("Tuples in "+r+":");
            final int MAX = 100;
            int num = MAX;
            TupleIterator j = r.iterator();
            while (j.hasNext()) {
                if (--num < 0) break;
                long[] a = j.nextTuple();
                out.print("\t(");
                for (int k = 0; k < a.length; ++k) {
                    if (k > 0) out.print(',');
                    Attribute at = r.getAttribute(k);
                    out.print(at);
                    out.print('=');
                    out.print(at.attributeDomain.toString((int) a[k]));
                    if (at.attributeDomain.map != null &&
                        a[k] >= 0 && a[k] < at.attributeDomain.map.size()) {
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
        for (Iterator i = relationsToDumpNegated.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping negated BDD for " + r);
            r.saveNegated();
        }
        for (Iterator i = relationsToDumpTuples.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping tuples for " + r);
            r.saveTuples();
        }
        for (Iterator i = relationsToDumpNegatedTuples.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            if (NOISY) out.println("Dumping negated tuples for " + r);
            r.saveNegatedTuples();
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
}
