// BDDSolver.java, created Mar 16, 2004 12:49:19 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.math.BigInteger;
import org.sf.bddbddb.ir.BDDInterpreter;
import org.sf.bddbddb.ir.IR;
import org.sf.bddbddb.util.AppendIterator;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.ListFactory;
import org.sf.bddbddb.util.MultiMap;
import org.sf.bddbddb.util.Pair;
import org.sf.bddbddb.util.PermutationGenerator;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;

/**
 * BDDSolver
 * 
 * @author jwhaley
 * @version $Id$
 */
public class BDDSolver extends Solver {
    public static String bddDomainInfoFileName = System.getProperty("bddinfo", "bddinfo");
    BDDFactory bdd;
    MultiMap fielddomainsToBDDdomains;
    Map orderingConstraints;
    int BDDNODES = Integer.parseInt(System.getProperty("bddnodes", "1000000"));
    int BDDCACHE = Integer.parseInt(System.getProperty("bddcache", "100000"));
    int BDDMINFREE = Integer.parseInt(System.getProperty("bddminfree", "20"));
    public String VARORDER = System.getProperty("bddvarorder", null);

    /**
     *  
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
        loadBDDDomainInfo();
        super.initialize();
        setVariableOrdering();
        initialize2(); // Do some more initialization after variable ordering is
        // set.
    }

    /**
     *  
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
     *  
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
        for (Iterator i = notequivalenceRelations.values().iterator(); i.hasNext();) {
            BDDRelation r = (BDDRelation) i.next();
            r.initialize2();
        }
    }

    /**
     *  
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
     *  
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

    /**
     * @throws IOException
     */
    void saveBDDDomainInfo() throws IOException {
        DataOutputStream dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(basedir + "r" + bddDomainInfoFileName));
            for (int i = 0; i < bdd.numberOfDomains(); ++i) {
                BDDDomain d = bdd.getDomain(i);
                for (Iterator j = fielddomainsToBDDdomains.keySet().iterator(); j.hasNext();) {
                    Domain fd = (Domain) j.next();
                    if (fielddomainsToBDDdomains.getValues(fd).contains(d)) {
                        dos.writeBytes(fd.toString() + "\n");
                        break;
                    }
                }
            }
        } finally {
            if (dos != null) dos.close();
        }
    }

    /**
     * @param name
     * @param bits
     * @return
     */
    BDDDomain makeDomain(String name, int bits) {
        Assert._assert(bits < 64);
        BDDDomain d = bdd.extDomain(new long[]{1L << bits})[0];
        d.setName(name);
        return d;
    }

    /**
     * @param dom
     * @return
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
     * @param dom
     * @return
     */
    public Collection getBDDDomains(Domain dom) {
        return fielddomainsToBDDdomains.getValues(dom);
    }

    /**
     * @param dom
     * @param k
     * @return
     */
    public BDDDomain getBDDDomain(Domain dom, int k) {
        List list = (List) fielddomainsToBDDdomains.getValues(dom);
        return (BDDDomain) list.get(k);
    }

    /**
     * @param s
     * @return
     */
    public BDDDomain getBDDDomain(String s) {
        for (int i = 0; i < bdd.numberOfDomains(); ++i) {
            BDDDomain d = bdd.getDomain(i);
            if (s.equals(d.getName())) return d;
        }
        return null;
    }

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
        bdd.done();
    }

    /**
     *  
     */
    void findPhysicalDomainMapping() {
        BDDFactory my_bdd = BDDFactory.init(100000, 10000);
        int BITS = BigInteger.valueOf(my_bdd.numberOfDomains()).bitLength();
        // one BDDDomain for each relation field.
        Set activeRelations = new HashSet();
        Map fieldOrVarToDomain = new HashMap();
        Map fieldOrVarToBDDDomain = new HashMap();
        for (Iterator i = rules.iterator(); i.hasNext();) {
            InferenceRule ir = (InferenceRule) i.next();
            for (Iterator j = new AppendIterator(ir.top.iterator(), Collections.singleton(ir.bottom).iterator()); j.hasNext();) {
                RuleTerm rt = (RuleTerm) j.next();
                if (activeRelations.add(rt.relation)) {
                    int x = 0;
                    for (Iterator k = rt.relation.attributes.iterator(); k.hasNext(); ++x) {
                        Attribute a = (Attribute) k.next();
                        Assert._assert(!fieldOrVarToDomain.containsKey(a));
                        Assert._assert(!fieldOrVarToBDDDomain.containsKey(a));
                        Domain fd = a.attributeDomain;
                        fieldOrVarToDomain.put(a, fd);
                        BDDDomain dom = makeDomain(my_bdd, a.toString(), BITS);
                        fieldOrVarToBDDDomain.put(a, dom);
                    }
                }
            }
        }
        // one BDDDomain for each necessary variable.
        for (Iterator i = rules.iterator(); i.hasNext();) {
            InferenceRule ir = (InferenceRule) i.next();
            for (Iterator j = new AppendIterator(ir.top.iterator(), Collections.singleton(ir.bottom).iterator()); j.hasNext();) {
                RuleTerm rt = (RuleTerm) j.next();
                for (int k = 0; k < rt.variables.size(); ++k) {
                    Variable v = (Variable) rt.variables.get(k);
                    if (!ir.necessaryVariables.contains(v)) continue;
                    Attribute a = (Attribute) rt.relation.attributes.get(k);
                    Domain fd = a.attributeDomain;
                    Domain fd2 = (Domain) fieldOrVarToDomain.get(v);
                    Assert._assert(fd2 == null || fd == fd2);
                    fieldOrVarToDomain.put(v, fd);
                    BDDDomain dom = (BDDDomain) fieldOrVarToBDDDomain.get(v);
                    if (dom == null) {
                        dom = makeDomain(my_bdd, v.toString(), BITS);
                        fieldOrVarToBDDDomain.put(v, dom);
                    }
                }
            }
        }
        BDD sol = my_bdd.one();
        // Every field and variable must be assigned to a physical domain
        // of the appropriate size.
        for (Iterator i = fieldOrVarToDomain.entrySet().iterator(); i.hasNext();) {
            Map.Entry e = (Map.Entry) i.next();
            BDDDomain my_d = (BDDDomain) fieldOrVarToBDDDomain.get(e.getKey());
            Domain fd = (Domain) e.getValue();
            Collection s = fielddomainsToBDDdomains.getValues(fd);
            BDD t = bdd.zero();
            for (Iterator j = s.iterator(); j.hasNext();) {
                BDDDomain d = (BDDDomain) j.next();
                int index = d.getIndex();
                t.orWith(my_d.ithVar(index));
            }
            sol.andWith(t);
        }
        // Every field of a particular relation must be assigned to different
        // physical domains.
        for (Iterator i = activeRelations.iterator(); i.hasNext();) {
            Relation r = (Relation) i.next();
            int x = 0;
            for (Iterator j = r.attributes.iterator(); j.hasNext(); ++x) {
                Attribute a = (Attribute) j.next();
                BDDDomain dom1 = (BDDDomain) fieldOrVarToBDDDomain.get(a);
                for (Iterator k = r.attributes.iterator(); k.hasNext();) {
                    Attribute a2 = (Attribute) k.next();
                    Domain fd2 = a2.attributeDomain;
                    BDDDomain dom2 = (BDDDomain) fieldOrVarToBDDDomain.get(a2);
                    BDD not_eq = dom1.buildEquals(dom2).not();
                    sol.andWith(not_eq);
                }
            }
        }
        // Every variable of a single rule must be assigned to a different
        // physical domain.
        for (Iterator i = rules.iterator(); i.hasNext();) {
            InferenceRule ir = (InferenceRule) i.next();
            for (Iterator j = ir.necessaryVariables.iterator(); j.hasNext();) {
                Variable v1 = (Variable) j.next();
                BDDDomain dom1 = (BDDDomain) fieldOrVarToBDDDomain.get(v1);
                for (Iterator k = ir.necessaryVariables.iterator(); k.hasNext();) {
                    Variable v2 = (Variable) k.next();
                    BDDDomain dom2 = (BDDDomain) fieldOrVarToBDDDomain.get(v2);
                    BDD not_eq = dom1.buildEquals(dom2).not();
                    sol.andWith(not_eq);
                }
            }
        }
        // Set user-specified domains.
        for (Iterator i = activeRelations.iterator(); i.hasNext();) {
            BDDRelation r = (BDDRelation) i.next();
            for (Iterator k = r.attributes.iterator(); k.hasNext();) {
                Attribute a = (Attribute) k.next();
                String name = a.attributeName;
                Domain fd = a.attributeDomain;
                String option = a.attributeOptions;
                if (option.equals("")) continue;
                if (!option.startsWith(fd.name)) throw new IllegalArgumentException("Field " + name + " has domain " + fd + ", but tried to assign "
                    + option);
                Collection doms = getBDDDomains(fd);
                BDDDomain d = null;
                for (Iterator j = doms.iterator(); j.hasNext();) {
                    BDDDomain dom = (BDDDomain) j.next();
                    if (dom.getName().equals(option)) {
                        d = dom;
                        break;
                    }
                }
                if (d == null) throw new IllegalArgumentException("Unknown BDD domain " + option);
                int index = d.getIndex();
                BDDDomain my_dom = (BDDDomain) fieldOrVarToBDDDomain.get(a);
                sol.andWith(my_dom.ithVar(index));
            }
        }
        System.out.println("Solutions to physical domain assignment constraint problem:\n   " + sol.toStringWithDomains());
        sol.free();
        my_bdd.done();
    }

    /**
     * @param bdd
     * @param name
     * @param bits
     * @return
     */
    static BDDDomain makeDomain(BDDFactory bdd, String name, int bits) {
        Assert._assert(bits < 64);
        BDDDomain d = bdd.extDomain(new long[]{1L << bits})[0];
        d.setName(name);
        return d;
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
     * @return
     */
    public BDDFactory getBDDFactory() {
        return this.bdd;
    }
}