// BDDSolver.java, created Mar 16, 2004 12:49:19 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import org.sf.bddbddb.ir.BDDInterpreter;
import org.sf.bddbddb.ir.IR;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.ListFactory;
import org.sf.bddbddb.util.MultiMap;
import org.sf.bddbddb.util.Pair;
import org.sf.bddbddb.util.PermutationGenerator;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;

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
    int BDDMINFREE = Integer.parseInt(System.getProperty("bddminfree", "20"));
    
    /**
     * BDD variable ordering.
     */
    public String VARORDER = System.getProperty("bddvarorder", null);

    /**
     * Constructs a new BDD solver.  Also initializes the BDD library.
     */
    public BDDSolver() {
        super();
        System.out.println("Initializing BDD library (" + BDDNODES + " nodes, cache size " + BDDCACHE + ", min free " + BDDMINFREE + "%)");
        bdd = BDDFactory.init(BDDNODES, BDDCACHE);
        fielddomainsToBDDdomains = new GenericMultiMap(ListFactory.linkedListFactory);
        orderingConstraints = new HashMap();
        bdd.setMaxIncrease(BDDNODES / 2);
        bdd.setMinFreeNodes(BDDMINFREE);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#initialize()
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
        for (Iterator i = equivalenceRelations.values().iterator(); i.hasNext();) {
            BDDRelation r = (BDDRelation) i.next();
            r.initialize2();
        }
    }

    /**
     * Set the BDD variable ordering based on VARORDER.
     */
    public void setVariableOrdering() {
        if (VARORDER != null) {
            fixVarOrder();
            System.out.print("Setting variable ordering to " + VARORDER + ", ");
            int[] varOrder = bdd.makeVarOrdering(true, VARORDER);
            bdd.setVarOrder(varOrder);
            System.out.println("done.");
        }
    }

    /**
     * Verify that the variable order is sane: Missing BDD domains are added and extra
     * BDD domains are removed.
     */
    void fixVarOrder() {
        // Verify that variable order is sane.
        StringTokenizer st = new StringTokenizer(VARORDER, "x_");
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
            System.out.println("Adding missing domain \"" + dName + "\" to bddvarorder.");
            String baseName = dName;
            for (;;) {
                char c = baseName.charAt(baseName.length() - 1);
                if (c < '0' || c > '9') break;
                baseName = baseName.substring(0, baseName.length() - 1);
            }
            int j = VARORDER.lastIndexOf(baseName);
            if (j <= 0) {
                VARORDER = dName + "_" + VARORDER;
            } else {
                char c = VARORDER.charAt(j - 1);
                VARORDER = VARORDER.substring(0, j) + dName + c + VARORDER.substring(j);
            }
        }
        for (Iterator i = domains.iterator(); i.hasNext();) {
            String dName = (String) i.next();
            System.out.println("Eliminating unused domain \"" + dName + "\" from bddvarorder.");
            int index = VARORDER.indexOf(dName);
            if (index == 0) {
                if (VARORDER.length() <= dName.length() + 1) {
                    VARORDER = "";
                } else {
                    VARORDER = VARORDER.substring(dName.length() + 1);
                }
            } else {
                char before = VARORDER.charAt(index - 1);
                int k = index + dName.length();
                if (before == '_' && k < VARORDER.length() && VARORDER.charAt(k) == 'x') {
                    // Case: H1_V1xV2 delete "V1x" substring
                    VARORDER = VARORDER.substring(0, index) + VARORDER.substring(k + 1);
                } else {
                    VARORDER = VARORDER.substring(0, index - 1) + VARORDER.substring(k);
                }
            }
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#solve()
     */
    public void solve() {
        Stratify s = new Stratify(this);
        s.stratify();
        if (USE_IR) {
            IR ir = IR.create(s);
            ir.optimize();
            if (PRINT_IR) ir.printIR();
            BDDInterpreter interpreter = new BDDInterpreter(ir);
            interpreter.interpret();
        } else {
            s.solve();
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#finish()
     */
    public void finish() {
        try {
            saveBDDDomainInfo();
        } catch (IOException x) {
        }
        calcOrderConstraints();
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.Solver#cleanup()
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
     * @see org.sf.bddbddb.Solver#createInferenceRule(java.util.List,
     *      org.sf.bddbddb.RuleTerm)
     */
    public InferenceRule createInferenceRule(List top, RuleTerm bottom) {
        return new BDDInferenceRule(this, top, bottom);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#createRelation(java.lang.String,
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

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#createEquivalenceRelation(org.sf.bddbddb.Domain)
     */
    Relation createEquivalenceRelation(Domain fd) {
        String name = fd + "_eq";
        Attribute a1 = new Attribute(fd + "1", fd, "");
        Attribute a2 = new Attribute(fd + "2", fd, "");
        BDDRelation r = new BDDRelation(this, name, new Pair(a1, a2));
        return r;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#createNotEquivalenceRelation(org.sf.bddbddb.Domain)
     */
    Relation createNotEquivalenceRelation(Domain fd) {
        String name = fd + "_neq";
        Attribute a1 = new Attribute(fd + "1", fd, "");
        Attribute a2 = new Attribute(fd + "2", fd, "");
        BDDRelation r = new BDDRelation(this, name, new Pair(a1, a2));
        return r;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#saveResults()
     */
    void saveResults() throws IOException {
        super.saveResults();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Solver#reportStats()
     */
    public void reportStats() {
        int final_node_size = bdd.getNodeNum();
        int final_table_size = bdd.getAllocNum();
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
    
    // FindBestOrder stuff below.
    Map orderingConstraints;
    
    /**
     *  
     */
    void calcOrderConstraints() {
        if (orderingConstraints.isEmpty()) return;
        System.out.println("Ordering constraints: " + orderingConstraints);
        Set allDomains = new HashSet();
        for (Iterator i = orderingConstraints.keySet().iterator(); i.hasNext();) {
            List list = (List) i.next();
            allDomains.addAll(list);
        }
        List domains = new ArrayList(allDomains);
        PermutationGenerator g = new PermutationGenerator(domains.size());
        List best = null;
        long bestTime = Long.MAX_VALUE;
        while (g.hasMore()) {
            int[] p = g.getNext();
            List domains2 = new ArrayList(p.length);
            for (int k = 0; k < p.length; ++k) {
                domains2.add(domains.get(p[k]));
            }
            long totalTime = 0L;
            for (Iterator i = orderingConstraints.entrySet().iterator(); i.hasNext();) {
                Map.Entry e = (Map.Entry) i.next();
                // Check if this ordering constraint matches p.
                List key = (List) e.getKey();
                if (doesOrderMatch(domains2, key)) {
                    //System.out.println(e);
                    totalTime += ((Long) e.getValue()).longValue();
                    if (totalTime < 0) totalTime = Long.MAX_VALUE;
                }
            }
            if (false || totalTime < bestTime) {
                System.out.print("Order: " + domains2);
                System.out.println(" Time: " + totalTime + " ms");
            }
            if (totalTime < bestTime) {
                best = domains2;
                bestTime = totalTime;
            }
        }
        System.out.print("Best order: " + best);
        System.out.println(" Time: " + bestTime + " ms");
    }
    static final Long MAX = new Long(Long.MAX_VALUE);

    /**
     * @param doms
     * @param time
     */
    void registerOrderConstraint(List doms, long time) {
        if (time == Long.MAX_VALUE) {
            System.out.println("Invalidating " + doms);
            // special case, obliterate all matching orders.
            for (Iterator i = orderingConstraints.entrySet().iterator(); i.hasNext();) {
                Map.Entry e = (Map.Entry) i.next();
                List list = (List) e.getKey();
                if (doesOrderMatch(list, doms)) {
                    if (!e.getValue().equals(MAX)) {
                        System.out.println("Invalidating " + doms + " also invalidates " + list);
                    }
                    e.setValue(MAX);
                } else {
                    //System.out.println("orders don't match. "+list+" and
                    // "+doms);
                }
            }
            orderingConstraints.put(doms, MAX);
        } else {
            Long t = (Long) orderingConstraints.get(doms);
            if (t == null) {
                orderingConstraints.put(doms, new Long(time));
            } else {
                time = t.longValue() + time;
                if (time < 0L) orderingConstraints.put(doms, MAX);
                else orderingConstraints.put(doms, new Long(time));
            }
        }
    }

    // returns true if a implies b
    static boolean doesOrderMatch(List a, List b) {
        Iterator i = a.iterator();
        Iterator j = b.iterator();
        for (;;) {
            if (!i.hasNext()) return !j.hasNext();
            if (!j.hasNext()) return true;
            Object c = i.next();
            Object d = j.next();
            for (;;) {
                if (c == d) break;
                if (!i.hasNext()) return false;
                c = i.next();
            }
        }
    }

    /**
     * @param doms
     * @return
     */
    long getOrderConstraint(List doms) {
        Long t = (Long) orderingConstraints.get(doms);
        if (t == null) {
            // check if it matches an invalidated one.
            for (Iterator i = orderingConstraints.entrySet().iterator(); i.hasNext();) {
                Map.Entry e = (Map.Entry) i.next();
                if (!e.getValue().equals(MAX)) continue;
                // Check if this ordering constraint matches p.
                List key = (List) e.getKey();
                if (doesOrderMatch(doms, key)) {
                    System.out.println("Order " + doms + " invalidated by " + key);
                    orderingConstraints.put(doms, MAX);
                    return Long.MAX_VALUE;
                }
            }
            return 0L;
        } else {
            return t.longValue();
        }
    }

}
