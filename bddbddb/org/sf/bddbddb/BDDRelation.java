// BDDRelation.java, created Mar 16, 2004 12:40:26 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.StringTokenizer;

import org.sf.bddbddb.util.Assert;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;
import org.sf.javabdd.BDD.BDDIterator;

/**
 * An implementation of Relation that uses BDDs.
 * 
 * @author jwhaley
 * @version $Id$
 */
public class BDDRelation extends Relation {
    
    /**
     * Link to solver.
     */
    protected BDDSolver solver;
    
    /**
     * Value of relation.
     */
    protected BDD relation;
    
    /**
     * List of BDDDomains that are used in this relation.
     * The indices coincide with those of the attributes.
     */
    protected List/*<BDDDomain>*/ domains;
    
    /**
     * Cache of the BDD set.
     */
    private BDD domainSet;

    /**
     * Construct a new BDDRelation.
     * This is only to be called internally.
     * 
     * @param solver  solver
     * @param name  name of relation
     * @param attributes  list of attributes for relation
     */
    BDDRelation(BDDSolver solver, String name, List attributes) {
        super(solver, name, attributes);
        this.solver = solver;
        if (solver.TRACE) solver.out.println("Created BDDRelation " + this);
    }

    /*
     * (non-Javadoc)
     * Called before variable order is set.
     * 
     * @see org.sf.bddbddb.Relation#initialize()
     */
    public void initialize() {
        if (isInitialized) return;
        if (negated != null && name.startsWith("!")) {
            if (solver.TRACE) solver.out.println("Skipping initialization of negated BDDRelation " + name);
            if (solver.TRACE) solver.out.println(" because normal " + negated.name + " is/will be initialized.");
            return;
        }
        this.relation = solver.bdd.zero();
        this.domains = new LinkedList();
        if (solver.TRACE) solver.out.println("Initializing BDDRelation " + name + " with attributes " + attributes);
        this.domainSet = solver.bdd.one();
        for (Iterator i = attributes.iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            Domain fd = a.attributeDomain;
            Collection doms = solver.getBDDDomains(fd);
            BDDDomain d = null;
            String option = a.attributeOptions;
            if (option != null && option.length() > 0) {
                // use the given domain.
                if (!option.startsWith(fd.name)) throw new IllegalArgumentException("Attribute " + a + " has domain " + fd + ", but tried to assign "
                    + option);
                //int index =
                // Integer.parseInt(option.substring(fd.name.length()));
                for (Iterator j = doms.iterator(); j.hasNext();) {
                    BDDDomain dom = (BDDDomain) j.next();
                    if (dom.getName().equals(option)) {
                        if (domains.contains(dom)) {
                            System.out.println("Cannot assign " + dom + " to attribute " + a + ": " + dom + " is already assigned");
                            option = "";
                            break;
                        } else {
                            d = dom;
                            break;
                        }
                    }
                }
                if (option.length() > 0) {
                    while (d == null) {
                        BDDDomain dom = solver.allocateBDDDomain(fd);
                        if (dom.getName().equals(option)) {
                            d = dom;
                            break;
                        }
                    }
                }
            }
            if (d == null) {
                // find an applicable domain.
                for (Iterator j = doms.iterator(); j.hasNext();) {
                    BDDDomain dom = (BDDDomain) j.next();
                    if (!domains.contains(dom)) {
                        d = dom;
                        break;
                    }
                }
                if (d == null) {
                    d = solver.allocateBDDDomain(fd);
                }
            }
            if (solver.TRACE) solver.out.println("Attribute " + a + " (" + a.attributeDomain + ") assigned to BDDDomain " + d);
            domains.add(d);
            domainSet.andWith(d.set());
        }
        if (negated != null) {
            BDDRelation bddn = (BDDRelation) negated;
            bddn.relation = solver.bdd.one();
            bddn.domains = this.domains;
            bddn.domainSet = this.domainSet;
            bddn.isInitialized = true;
        }
        isInitialized = true;
    }

    /**
     * (Re-)calculate the domain set. 
     * 
     * @return  the domain set
     */
    BDD calculateDomainSet() {
        if (domainSet != null) domainSet.free();
        this.domainSet = solver.bdd.one();
        for (Iterator i = domains.iterator(); i.hasNext();) {
            BDDDomain d = (BDDDomain) i.next();
            domainSet.andWith(d.set());
        }
        return domainSet;
    }

    /**
     * Do more initialization.  This initializes the values of equivalence relations.
     * Called after variable order is set, so the computation is faster.
     */
    public void initialize2() {
        Assert._assert(isInitialized);
        boolean is_equiv = solver.equivalenceRelations.values().contains(this);
        boolean is_lt = solver.lessThanRelations.values().contains(this);
        boolean is_gt = solver.greaterThanRelations.values().contains(this);
        if (is_equiv || is_lt || is_gt) {
            BDDDomain d1 = (BDDDomain) domains.get(0);
            BDDDomain d2 = (BDDDomain) domains.get(1);
            relation.free();
            BDD b;
            if (is_equiv) {
                b = d1.buildEquals(d2);
            } else if (is_lt) {
                b = buildLessThan(d1,d2);
            } else {
                b = buildLessThan(d2,d1);
            }
            
            relation = b;
            if (negated != null) {
                BDDRelation bddn = (BDDRelation) negated;
                bddn.relation.free();
                bddn.relation = b.not();
            }
        }
    }

    /**
     * build d1 < d2
     * @param d1
     * @param d2
     * @return
     */
    private BDD buildLessThan(BDDDomain d1, BDDDomain d2) {
        BDD leftwardBitsEqual = solver.bdd.one();
        BDD result = solver.bdd.zero();
        for (long i=d1.size()-1; i>=0; i--) {
            BDD v1 = d1.ithVar(i);
            BDD v2 = d2.ithVar(i);
            result.orWith(v2.and(v1.not()).and(leftwardBitsEqual));
            leftwardBitsEqual.andWith(v1.biimp(v2));
        }        
        return result;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#load()
     */
    public void load() throws IOException {
        load(solver.basedir + name + ".bdd");
        if (solver.NOISY) solver.out.println("Loaded BDD from file: " + name + ".bdd " + relation.nodeCount() + " nodes, " + dsize() + " elements.");
        if (solver.NOISY) solver.out.println("Domains of loaded relation:" + activeDomains(relation));
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#loadTuples()
     */
    public void loadTuples() throws IOException {
        loadTuples(solver.basedir + name + ".tuples");
        if (solver.NOISY) solver.out.println("Loaded tuples from file: " + name + ".tuples");
        if (solver.NOISY) solver.out.println("Domains of loaded relation:" + activeDomains(relation));
    }

    /**
     * Updated the negated form of this relation.
     */
    void updateNegated() {
        if (negated != null) {
            BDDRelation bddn = (BDDRelation) negated;
            bddn.relation.free();
            bddn.relation = relation.not();
        }
    }

    /**
     * Load this relation from the given file.
     * 
     * @param filename  the file to load
     * @throws IOException
     */
    public void load(String filename) throws IOException {
        Assert._assert(isInitialized);
        BDD r2 = solver.bdd.load(filename);
        if (r2 != null) {
            if (r2.isZero()) {
                System.out.println("Warning: " + filename + " is zero.");
            } else if (r2.isOne()) {
                System.out.println("Warning: " + filename + " is one.");
            } else {
                BDD s = r2.support();
                calculateDomainSet();
                BDD t = domainSet.and(s);
                s.free();
                boolean b = !t.equals(domainSet);
                t.free();
                if (b) {
                    throw new IOException("Expected domains for loaded BDD " + filename + " to be " + domains + ", but found " + activeDomains(r2)
                        + " instead");
                }
            }
            relation.free();
            relation = r2;
        }
        updateNegated();
    }

    /**
     * Verify that the domains for this BDD are correct.
     * 
     * @return  whether the domains are correct
     */
    public boolean verify() {
        BDD s = relation.support();
        calculateDomainSet();
        BDD t = domainSet.and(s);
        s.free();
        boolean result = t.equals(domainSet);
        if (!result) {
            System.out.println("Warning, domains for " + this + " don't match BDD: " + activeDomains(relation) + " vs " + domains);
        }
        return result;
    }

    /**
     * Load this relation in tuple form from the given file.
     * 
     * @param filename  the file to load
     * @throws IOException
     */
    public void loadTuples(String filename) throws IOException {
        Assert._assert(isInitialized);
        BufferedReader in = null;
        try {
            in = new BufferedReader(new FileReader(filename));
            for (;;) {
                String s = in.readLine();
                if (s == null) break;
                if (s.length() == 0) continue;
                if (s.startsWith("#")) continue;
                StringTokenizer st = new StringTokenizer(s);
                BDD b = solver.bdd.one();
                for (int i = 0; i < domains.size(); ++i) {
                    BDDDomain d = (BDDDomain) domains.get(i);
                    String v = st.nextToken();
                    if (v.equals("*")) {
                        b.andWith(d.domain());
                    } else {
                        int x = v.indexOf('-');
                        if (x < 0) {
                            long l = Long.parseLong(v);
                            b.andWith(d.ithVar(l));
                            if (solver.TRACE_FULL) solver.out.print(attributes.get(i) + ": " + l + ", ");
                        } else {
                            long l = Long.parseLong(v.substring(0, x));
                            long m = Long.parseLong(v.substring(x + 1));
                            b.andWith(d.varRange(l, m));
                            if (solver.TRACE_FULL) solver.out.print(attributes.get(i) + ": " + l + "-" + m + ", ");
                        }
                    }
                }
                if (solver.TRACE_FULL) solver.out.println();
                relation.orWith(b);
            }
        } finally {
            if (in != null) in.close();
        }
        updateNegated();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#save()
     */
    public void save() throws IOException {
        save(solver.basedir + name + ".rbdd");
    }

    /**
     * Save the value of this relation to the given file.
     * 
     * @param filename  name of file to save
     * @throws IOException
     */
    public void save(String filename) throws IOException {
        Assert._assert(isInitialized);
        System.out.println("Relation " + this + ": " + relation.nodeCount() + " nodes, " + dsize() + " elements");
        solver.bdd.save(filename, relation);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#saveNegated()
     */
    public void saveNegated() throws IOException {
        Assert._assert(isInitialized);
        System.out.println("Relation " + this + ": " + relation.not().nodeCount() + " nodes");
        solver.bdd.save(solver.basedir + "not" + name + ".rbdd", relation.not());
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#saveTuples()
     */
    public void saveTuples() throws IOException {
        saveTuples(solver.basedir + name + ".rtuples", relation);
    }

    /**
     * Save the value of this relation in tuple form to the given file.
     * 
     * @param filename  name of file to save
     * @throws IOException
     */
    public void saveTuples(String filename) throws IOException {
        System.out.println("Relation " + this + ": " + relation.nodeCount() + " nodes, " + dsize() + " elements");
        saveTuples(solver.basedir + name + ".rtuples", relation);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#saveNegatedTuples()
     */
    public void saveNegatedTuples() throws IOException {
        System.out.println("Relation " + this + ": " + relation.nodeCount() + " nodes");
        saveTuples(solver.basedir + "not" + name + ".rtuples", relation.not());
    }

    /**
     * Save the given relation in tuple form to the given file.
     * 
     * @param fileName  name of file to save
     * @param relation  value to save
     * @throws IOException
     */
    public void saveTuples(String fileName, BDD relation) throws IOException {
        Assert._assert(isInitialized);
        BufferedWriter dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(fileName));
            if (relation.isZero()) {
                return;
            }
            BDD allDomains = solver.bdd.one();
            dos.write("#");
            System.out.print(fileName + " domains {");
            int[] domIndices = new int[domains.size()];
            int k = -1;
            for (Iterator i = domains.iterator(); i.hasNext();) {
                BDDDomain d = (BDDDomain) i.next();
                System.out.print(" " + d.toString());
                dos.write(" " + d.toString() + ":" + d.varNum());
                domIndices[++k] = d.getIndex();
            }
            dos.write("\n");
            System.out.println(" } = " + relation.nodeCount() + " nodes, " + dsize() + " elements");
            if (relation.isOne()) {
                for (k = 0; k < domIndices.length; ++k) {
                    dos.write("* ");
                }
                dos.write("\n");
                return;
            }
            
           calculateDomainSet();
           int lines = 0;
           BDDIterator i = relation.iterator(domainSet);
            while (i.hasNext()) {
                BDD sat = (BDD) i.next();
                long[] v = sat.scanAllVar();
                for (k = 0; k < domIndices.length; ++k) {
                    long val = v[domIndices[k]];
                    if (val == 0L) {
                        // Check if this is the universal set.
                        BDDDomain d = solver.bdd.getDomain(domIndices[k]);
                        if (i.isDontCare(d)) {
                            i.skipDontCare(d);
                            dos.write("* ");
                            continue;
                        }
                    }
                    dos.write(val + " ");
                }
                dos.write("\n");
                ++lines;
            }
            System.out.println("Done writing " + lines + " lines.");
        } finally {
            if (dos != null) dos.close();
        }
    }

    /**
     * Return a string representation of the active domains of the given relation.
     * 
     * @param relation  relation to check
     * @return  string representation of the active domains
     */
    public static String activeDomains(BDD relation) {
        BDDFactory bdd = relation.getFactory();
        BDD s = relation.support();
        int[] a = s.scanSetDomains();
        s.free();
        if (a == null) return "(none)";
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < a.length; ++i) {
            sb.append(bdd.getDomain(a[i]));
            if (i < a.length - 1) sb.append(',');
        }
        return sb.toString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#dsize()
     */
    public double dsize() {
        calculateDomainSet();
        return relation.satCount(domainSet);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#iterator()
     */
    public TupleIterator iterator() {
        calculateDomainSet();
        final Iterator i = relation.iterator(domainSet);
        return new MyTupleIterator(i, domains);
    }
    
    /**
     * Implementation of TupleIterator for BDDs.
     */
    static class MyTupleIterator extends TupleIterator {
        protected Iterator i;
        protected List domains;

        protected MyTupleIterator(Iterator i, List domains) {
            this.i = i;
            this.domains = domains;
        }

        public long[] nextTuple() {
            BDD b = (BDD) i.next();
            long[] r = new long[domains.size()];
            long[] q = b.scanAllVar();
            int j = 0;
            for (Iterator k = domains.iterator(); k.hasNext(); ++j) {
                BDDDomain d = (BDDDomain) k.next();
                r[j] = q[d.getIndex()];
            }
            return r;
        }

        public boolean hasNext() {
            return i.hasNext();
        }

        public void remove() {
            i.remove();
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#iterator(int)
     */
    public TupleIterator iterator(int k) {
        final BDDDomain d = (BDDDomain) domains.get(k);
        BDD s = d.set();
        final Iterator i = relation.iterator(s);
        return new TupleIterator() {
            public long[] nextTuple() {
                BDD b = (BDD) i.next();
                long v = b.scanVar(d);
                return new long[]{v};
            }

            public boolean hasNext() {
                return i.hasNext();
            }

            public void remove() {
                i.remove();
            }
        };
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#iterator(int, long)
     */
    public TupleIterator iterator(int k, long j) {
        final BDDDomain d = (BDDDomain) domains.get(k);
        BDD val = d.ithVar(j);
        val.andWith(relation.id());
        calculateDomainSet();
        final Iterator i = val.iterator(domainSet);
        return new MyTupleIterator(i, domains);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#iterator(long[])
     */
    public TupleIterator iterator(long[] j) {
        BDD val = relation.id();
        for (int i = 0; i < j.length; ++i) {
            if (j[i] == -1) continue;
            final BDDDomain d = (BDDDomain) domains.get(i);
            val.andWith(d.ithVar(j[i]));
        }
        calculateDomainSet();
        final Iterator i = val.iterator(domainSet);
        return new MyTupleIterator(i, domains);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#contains(int, long)
     */
    public boolean contains(int k, long j) {
        final BDDDomain d = (BDDDomain) domains.get(k);
        BDD b = relation.id();
        b.restrictWith(d.ithVar(j));
        boolean result = b.isZero();
        b.free();
        return result;
    }

    /**
     * Return the value of this relation in BDD form.
     * 
     * @return BDD form of this relation
     */
    public BDD getBDD() {
        return relation;
    }

    /**
     * Set the value of this relation from the given BDD.
     * 
     * @param b  BDD value to set from
     */
    public void setBDD(BDD b) {
        if (relation != null) relation.free();
        relation = b;
    }

    /**
     * Get the BDDDomain with the given index.
     * 
     * @param i  index
     * @return  BDDDomain at that index
     */
    public BDDDomain getBDDDomain(int i) {
        return (BDDDomain) domains.get(i);
    }

    /**
     * Get the BDDDomain that matches the given attribute.
     * 
     * @param a  attribute
     * @return  BDDDomain that matches that attribute
     */
    public BDDDomain getBDDDomain(Attribute a) {
        int i = attributes.indexOf(a);
        if (i == -1) return null;
        return (BDDDomain) domains.get(i);
    }
    
    public Attribute getAttribute(BDDDomain d){
       int i = domains.indexOf(d);
       if(i == -1) return null;
       return (Attribute) attributes.get(i);
    }

    /**
     * Returns the list of BDD domains this relation is using.
     * 
     * @return  the list of BDDDomains this relation is using
     */
    public List getBDDDomains() {
        return domains;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#copy()
     */
    public Relation copy() {
        List a = new LinkedList(attributes);
        Relation that = solver.createRelation(name + '\'', a);
        return that;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#free()
     */
    public void free() {
        if (relation != null) {
            relation.free();
            relation = null;
        }
        if (domainSet != null) {
            domainSet.free();
            domainSet = null;
        }
    }

    /**
     * Set the BDD domain assignment of this relation to the given one.
     * 
     * @param newdom  new BDD domain assignment
     */
    public void setDomainAssignment(List newdom) {
        Assert._assert(newdom.size() == attributes.size());
        Assert._assert(new HashSet(newdom).size() == newdom.size(), newdom.toString());
        for (int i = 0; i < newdom.size(); ++i) {
            Domain d = ((Attribute) attributes.get(i)).getDomain();
            Assert._assert(solver.getBDDDomains(d).contains(newdom.get(i)));
        }
        this.domains = newdom;
    }
}
