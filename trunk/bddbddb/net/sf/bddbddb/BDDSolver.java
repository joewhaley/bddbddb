// BDDSolver.java, created Mar 16, 2004 12:49:19 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.StringTokenizer;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import jwutil.collections.GenericMultiMap;
import jwutil.collections.ListFactory;
import jwutil.collections.MultiMap;
import jwutil.collections.Pair;
import jwutil.util.Assert;
import net.sf.bddbddb.Learner.IndividualRuleLearner;
import net.sf.bddbddb.ir.BDDInterpreter;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;

/**
 * An implementation of Solver that uses BDDs.
 * 
 * @author jwhaley
 * @version $Id$
 */
public class BDDSolver extends Solver {
    
    /**
     * Filename for BDD domain info file.
     * The BDD domain info file contains the list of domains that are allocated
     */
    public static String bddDomainInfoFileName = System.getProperty("bddinfo", "bddinfo");
    
    /**
     * Link to the BDD factory we use.
     */
    BDDFactory bdd;
    
    /**
     * Map from a field domain to the set of BDD domains we have allocated for that field domain.
     */
    MultiMap fielddomainsToBDDdomains;
    
    FindBestDomainOrder fbo;
    
    /**
     * Initial size of BDD node table.
     * You can set this with "-Dbddnodes=xxx"
     */
    int BDDNODES = Integer.parseInt(System.getProperty("bddnodes", "1000000"));
    
    /**
     * Initial size of BDD operation cache.
     * You can set this with "-Dbddcache=xxx"
     */
    int BDDCACHE = Integer.parseInt(System.getProperty("bddcache", "100000"));
    
    /**
     * BDD minimum free parameter.  This tells the BDD library when to grow the
     * node table.  You can set this with "-Dbddminfree=xxx"
     */
    double BDDMINFREE = Double.parseDouble(System.getProperty("bddminfree", ".20"));
    
    /**
     * BDD variable ordering.
     */
    public String VARORDER = System.getProperty("bddvarorder", null);

    public String TRIALFILE = System.getProperty("trialfile", null);
    
    /**
     * Constructs a new BDD solver.  Also initializes the BDD library.
     */
    public BDDSolver() {
        super();
        System.out.println("Initializing BDD library (" + BDDNODES + " nodes, cache size " + BDDCACHE + ", min free " + BDDMINFREE + "%)");
        bdd = BDDFactory.init(1000, BDDCACHE);
        fielddomainsToBDDdomains = new GenericMultiMap(ListFactory.linkedListFactory);
        bdd.setMinFreeNodes(BDDMINFREE);
        fbo = new FindBestDomainOrder(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.Solver#initialize()
     */
    public void initialize() {
        if (!isInitialized)
            loadBDDDomainInfo();
        super.initialize();
        if (!isInitialized) {
            setVariableOrdering();
        }
        initialize2(); // Do some more initialization after variable ordering is set.
        isInitialized = true;
        
        if (TRIALFILE == null && inputFilename != null) {
            String sep = System.getProperty("file.separator");
            int index1 = inputFilename.lastIndexOf(sep) + 1;
            if (index1 == 0) index1 = inputFilename.lastIndexOf('/') + 1;
            int index2 = inputFilename.lastIndexOf('.');
            if (index1 < index2)
                TRIALFILE = "trials_"+inputFilename.substring(index1, index2)+".xml";
        }
        if (TRIALFILE != null) fbo.loadTrials(TRIALFILE);
    }

    public String getBaseName() {
        if (inputFilename == null) return null;
        String sep = System.getProperty("file.separator");
        int index1 = inputFilename.lastIndexOf(sep) + 1;
        if (index1 == 0) index1 = inputFilename.lastIndexOf('/') + 1;
        int index2 = inputFilename.lastIndexOf('.');
        if (index1 < index2)
            return inputFilename.substring(index1, index2);
        else
            return null;
    }
    
    /**
     * Load the BDD domain info, if it exists.
     * The domain info is the list of domains that are allocated.
     */
    void loadBDDDomainInfo() {
        BufferedReader in = null;
        try {
            in = new BufferedReader(new FileReader(basedir + bddDomainInfoFileName));
            for (;;) {
                String s = in.readLine();
                if (s == null) break;
                if (s.length() == 0) continue;
                if (s.startsWith("#")) continue;
                StringTokenizer st = new StringTokenizer(s);
                String domain = st.nextToken();
                Domain fd = (Domain) nameToDomain.get(domain);
                allocateBDDDomain(fd);
            }
        } catch (IOException x) {
        } finally {
            if (in != null) try {
                in.close();
            } catch (IOException _) {
            }
        }
    }

    /**
     * Initialize the values of equivalence relations.
     */
    public void initialize2() {
        for (Iterator i = nameToRelation.values().iterator(); i.hasNext();) {
            BDDRelation r = (BDDRelation) i.next();
            r.initialize2();
        }
    }

    /**
     * Set the BDD variable ordering based on VARORDER.
     */
    public void setVariableOrdering() {
        if (VARORDER != null) {
            VARORDER = fixVarOrder(VARORDER, true);
            System.out.print("Setting variable ordering to " + VARORDER + ", ");
            int[] varOrder = bdd.makeVarOrdering(true, VARORDER);
            bdd.setVarOrder(varOrder);
            System.out.println("done.");
            // Grow variable table after setting var order.
            bdd.setNodeTableSize(BDDNODES);
        }
    }

    /**
     * Verify that the variable order is sane: Missing BDD domains are added and extra
     * BDD domains are removed.
     */
    String fixVarOrder(String varOrder, boolean trace) {
        // Verify that variable order is sane.
        StringTokenizer st = new StringTokenizer(varOrder, "x_");
        List domains = new LinkedList();
        while (st.hasMoreTokens()) {
            domains.add(st.nextToken());
        }
        for (int i = 0; i < bdd.numberOfDomains(); ++i) {
            String dName = bdd.getDomain(i).getName();
            if (domains.contains(dName)) {
                domains.remove(dName);
                continue;
            }
            if (trace) System.out.println("Adding missing domain \"" + dName + "\" to bddvarorder.");
            String baseName = dName;
            for (;;) {
                char c = baseName.charAt(baseName.length() - 1);
                if (c < '0' || c > '9') break;
                baseName = baseName.substring(0, baseName.length() - 1);
            }
            int j = varOrder.lastIndexOf(baseName);
            if (j <= 0) {
                varOrder = dName + "_" + varOrder;
            } else {
                char c = varOrder.charAt(j - 1);
                varOrder = varOrder.substring(0, j) + dName + c + varOrder.substring(j);
            }
        }
        for (Iterator i = domains.iterator(); i.hasNext();) {
            String dName = (String) i.next();
            if (trace) System.out.println("Eliminating unused domain \"" + dName + "\" from bddvarorder.");
            int index = varOrder.indexOf(dName);
            if (index == 0) {
                if (varOrder.length() <= dName.length() + 1) {
                    varOrder = "";
                } else {
                    varOrder = varOrder.substring(dName.length() + 1);
                }
            } else {
                char before = varOrder.charAt(index - 1);
                int k = index + dName.length();
                if (before == '_' && k < varOrder.length() && varOrder.charAt(k) == 'x') {
                    // Case: H1_V1xV2 delete "V1x" substring
                    varOrder = varOrder.substring(0, index) + varOrder.substring(k + 1);
                } else {
                    varOrder = varOrder.substring(0, index - 1) + varOrder.substring(k);
                }
            }
        }
        return varOrder;
    }

    /* (non-Javadoc)
     * @see net.sf.bddbddb.Solver#solve()
     */
    public void solve() {
        if (USE_IR) {
            BDDInterpreter interpreter = new BDDInterpreter(ir);
            interpreter.interpret();
            //stratify.solve();
        } else {
            IterationList list = ifg.getIterationList();
            //System.out.println(list);
            BDDInterpreter interpreter = new BDDInterpreter(null);
            long time = System.currentTimeMillis();
            interpreter.interpret(list);
            if (LEARN_BEST_ORDER) {
                time = System.currentTimeMillis() - time;
                System.out.println("SOLVE_TIME: " + time);
                reportStats();
                Learner learner = new IndividualRuleLearner(this, stratify);
                learner.learn();
            }
        }
    }
    
    public List rulesToLearn(){
        List rulesToLearn = new LinkedList();
        for(Iterator it = rules.iterator(); it.hasNext(); ){
            BDDInferenceRule rule = (BDDInferenceRule) it.next();
            if(LEARN_ALL_RULES || rule.learn_best_order) rulesToLearn.add(rule);     
        }  
        return rulesToLearn;
    }
    
    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.Solver#finish()
     */
    public void finish() {
        try {
            saveBDDDomainInfo();
        } catch (IOException x) {
        }
        fbo.dump();
    }

    /* (non-Javadoc)
     * @see net.sf.bddbddb.Solver#cleanup()
     */
    public void cleanup() {
        bdd.done();
    }
    
    /**
     * Save the BDD domain info.
     * 
     * @throws IOException
     */
    void saveBDDDomainInfo() throws IOException {
        BufferedWriter dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(basedir + "r" + bddDomainInfoFileName));
            for (int i = 0; i < bdd.numberOfDomains(); ++i) {
                BDDDomain d = bdd.getDomain(i);
                for (Iterator j = fielddomainsToBDDdomains.keySet().iterator(); j.hasNext();) {
                    Domain fd = (Domain) j.next();
                    if (fielddomainsToBDDdomains.getValues(fd).contains(d)) {
                        dos.write(fd.toString() + "\n");
                        break;
                    }
                }
            }
        } finally {
            if (dos != null) dos.close();
        }
    }

    /**
     * Make a BDD domain with the given name and number of bits.
     * 
     * @param name  name of BDD domain
     * @param bits  number of bits desired
     * @return  new BDD domain
     */
    BDDDomain makeDomain(String name, int bits) {
        Assert._assert(bits < 64);
        BDDDomain d = bdd.extDomain(new long[]{1L << bits})[0];
        d.setName(name);
        return d;
    }

    /**
     * Allocate a new BDD domain that matches the given domain.
     * 
     * @param dom  domain to match
     * @return  new BDD domain
     */
    public BDDDomain allocateBDDDomain(Domain dom) {
        int version = getBDDDomains(dom).size();
        int bits = BigInteger.valueOf(dom.size - 1).bitLength();
        BDDDomain d = makeDomain(dom.name + version, bits);
        if (TRACE) out.println("Allocated BDD domain " + d + ", size " + dom.size + ", " + bits + " bits.");
        fielddomainsToBDDdomains.add(dom, d);
        return d;
    }

    /**
     * Get the set of BDD domains allocated for a given domain.
     * 
     * @param dom  domain
     * @return  set of BDD domains
     */
    public Collection getBDDDomains(Domain dom) {
        return fielddomainsToBDDdomains.getValues(dom);
    }

    /**
     * Get the k-th BDD domain allocated for a given domain.
     * 
     * @param dom  domain
     * @param k  index
     * @return  k-th BDD domain allocated for the given domain
     */
    public BDDDomain getBDDDomain(Domain dom, int k) {
        List list = (List) fielddomainsToBDDdomains.getValues(dom);
        return (BDDDomain) list.get(k);
    }

    /**
     * Get the BDD domain with the given name.
     * 
     * @param s  name of BDD domain
     * @return  BDD domain with the given name
     */
    public BDDDomain getBDDDomain(String s) {
        for (int i = 0; i < bdd.numberOfDomains(); ++i) {
            BDDDomain d = bdd.getDomain(i);
            if (s.equals(d.getName())) return d;
        }
        return null;
    }

    /**
     * Return the map of field domains to sets of allocated BDD domains. 
     * 
     * @return  map between field domains and sets of allocated BDD domains
     */
    public MultiMap getBDDDomains() {
        return fielddomainsToBDDdomains;
    }

    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.Solver#createInferenceRule(java.util.List,
     *      net.sf.bddbddb.RuleTerm)
     */
    public InferenceRule createInferenceRule(List top, RuleTerm bottom) {
        return new BDDInferenceRule(this, top, bottom);
    }

    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.Solver#createRelation(java.lang.String,
     *      java.util.List, java.util.List, java.util.List)
     */
    public Relation createRelation(String name, List attributes) {
        while (nameToRelation.containsKey(name)) {
            name = mungeName(name);
        }
        return new BDDRelation(this, name, attributes);
    }

    /**
     * Munge the given name to be unique.
     * 
     * @param name  name of relation
     * @return  new unique name
     */
    String mungeName(String name) {
        return name + '#' + relations.size();
    }

    /* (non-Javadoc)
     * @see net.sf.bddbddb.Solver#createEquivalenceRelation(net.sf.bddbddb.Domain, net.sf.bddbddb.Domain)
     */
    Relation createEquivalenceRelation(Domain fd1, Domain fd2) {
        String name = fd1 + "_eq_" + fd2;
        Attribute a1 = new Attribute(fd1 + "_1", fd1, "");
        Attribute a2 = new Attribute(fd2 + "_2", fd2, "");
        BDDRelation r = new BDDRelation(this, name, new Pair(a1, a2));
        r.special_type = BDDRelation.EQ;
        return r;
    }

    /* (non-Javadoc)
     * @see net.sf.bddbddb.Solver#createLessThanRelation(net.sf.bddbddb.Domain, net.sf.bddbddb.Domain)
     */
    Relation createLessThanRelation(Domain fd1, Domain fd2) {
        String name = fd1 + "_lt_" + fd2;
        Attribute a1 = new Attribute(fd1 + "_1", fd1, "");
        Attribute a2 = new Attribute(fd2 + "_2", fd2, "");
        BDDRelation r = new BDDRelation(this, name, new Pair(a1, a2));
        r.special_type = BDDRelation.LT;
        return r;
    }

    /* (non-Javadoc)
     * @see net.sf.bddbddb.Solver#createGreaterThanRelation(net.sf.bddbddb.Domain, net.sf.bddbddb.Domain)
     */
    Relation createGreaterThanRelation(Domain fd1, Domain fd2) {
        String name = fd1 + "_gt_" + fd2;
        Attribute a1 = new Attribute(fd1 + "_1", fd1, "");
        Attribute a2 = new Attribute(fd2 + "_2", fd2, "");
        BDDRelation r = new BDDRelation(this, name, new Pair(a1, a2));
        r.special_type = BDDRelation.GT;
        return r;
    }
    
    /* (non-Javadoc)
     * @see net.sf.bddbddb.Solver#createMapRelation(net.sf.bddbddb.Domain, net.sf.bddbddb.Domain)
     */
    Relation createMapRelation(Domain fd1, Domain fd2) {
        String name = "map_" + fd1 + "_" + fd2;
        Attribute a1 = new Attribute(fd1.name, fd1, "");
        Attribute a2 = new Attribute(fd2.name, fd2, "");
        BDDRelation r = new BDDRelation(this, name, new Pair(a1, a2));
        r.special_type = BDDRelation.MAP;
        return r;
    }
    
    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.Solver#saveResults()
     */
    void saveResults() throws IOException {
        super.saveResults();
    }

    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.Solver#reportStats()
     */
    public void reportStats() {
        int final_node_size = bdd.getNodeNum();
        int final_table_size = bdd.getNodeTableSize();
        System.out.println("MAX_NODES=" + final_table_size);
        System.out.println("FINAL_NODES=" + final_node_size);
        super.reportStats();
    }

    /**
     * Get the BDD factory used by this solver.
     * 
     * @return  BDD factory
     */
    public BDDFactory getBDDFactory() {
        return this.bdd;
    }


    
}
