// BDDRelation.java, created Mar 16, 2004 12:40:26 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.StringTokenizer;
import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import org.sf.bddbddb.util.Assert;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;

/**
 * BDDRelation
 * 
 * @author jwhaley
 * @version $Id$
 */
public class BDDRelation extends Relation {
    BDDSolver solver;
    BDD relation;
    List/* <BDDDomain> */domains;
    private BDD domainSet;

    /**
     * @param solver
     * @param name
     * @param attributes
     */
    public BDDRelation(BDDSolver solver, String name, List attributes) {
        super(solver, name, attributes);
        this.solver = solver;
        if (solver.TRACE) solver.out.println("Created BDDRelation " + this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#initialize()
     */
    // Called before variable order is set.
    public void initialize() {
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
        }
    }

    public BDD calculateDomainSet() {
        if (domainSet != null) domainSet.free();
        this.domainSet = solver.bdd.one();
        for (Iterator i = domains.iterator(); i.hasNext();) {
            BDDDomain d = (BDDDomain) i.next();
            domainSet.andWith(d.set());
        }
        return domainSet;
    }

    /**
     *  
     */
    // Called after variable order is set.
    public void initialize2() {
        boolean is_equiv = solver.equivalenceRelations.values().contains(this);
        if (is_equiv) {
            BDDDomain d1 = (BDDDomain) domains.get(0);
            BDDDomain d2 = (BDDDomain) domains.get(1);
            relation.free();
            BDD b = d1.buildEquals(d2);
            relation = b;
            if (negated != null) {
                BDDRelation bddn = (BDDRelation) negated;
                bddn.relation.free();
                bddn.relation = b.not();
            }
        }
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
     *  
     */
    void updateNegated() {
        if (negated != null) {
            BDDRelation bddn = (BDDRelation) negated;
            bddn.relation.free();
            bddn.relation = relation.not();
        }
    }

    /**
     * @param filename
     * @throws IOException
     */
    public void load(String filename) throws IOException {
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
     * @param filename
     * @throws IOException
     */
    public void loadTuples(String filename) throws IOException {
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
     * @param filename
     * @throws IOException
     */
    public void save(String filename) throws IOException {
        System.out.println("Relation " + this + ": " + relation.nodeCount() + " nodes, " + dsize() + " elements");
        solver.bdd.save(filename, relation);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.Relation#saveNegated()
     */
    public void saveNegated() throws IOException {
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
     * @param fileName
     * @param relation
     * @throws IOException
     */
    public void saveTuples(String fileName, BDD relation) throws IOException {
        DataOutputStream dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(fileName));
            if (relation.isZero()) {
                return;
            }
            BDD ss = relation.support();
            int[] a = ss.scanSetDomains();
            ss.free();
            BDD allDomains = solver.bdd.one();
            dos.writeBytes("#");
            System.out.print(fileName + " domains {");
            for (Iterator i = domains.iterator(); i.hasNext();) {
                BDDDomain d = (BDDDomain) i.next();
                System.out.print(" " + d.toString());
                dos.writeBytes(" " + d.toString() + ":" + d.varNum());
            }
            dos.writeBytes("\n");
            System.out.println(" } = " + relation.nodeCount() + " nodes, " + dsize() + " elements");
            if (relation.isOne()) {
                for (Iterator j = domains.iterator(); j.hasNext();) {
                    BDDDomain d = (BDDDomain) j.next();
                    dos.writeBytes("* ");
                }
                dos.writeBytes("\n");
                return;
            }
            for (int i = 0; i < a.length; ++i) {
                BDDDomain d = solver.bdd.getDomain(a[i]);
                allDomains.andWith(d.set());
            }
            BDDDomain iterDomain = (BDDDomain) domains.get(0);
            BDD foo = relation.exist(allDomains.exist(iterDomain.set()));
            int lines = 0;
            for (Iterator i = foo.iterator(iterDomain.set()); i.hasNext();) {
                BDD q = (BDD) i.next();
                q.andWith(relation.id());
                while (!q.isZero()) {
                    BDD sat = q.satOne(allDomains, solver.bdd.zero());
                    BDD sup = q.support();
                    int[] b = sup.scanSetDomains();
                    sup.free();
                    long[] v = sat.scanAllVar();
                    sat.free();
                    BDD t = solver.bdd.one();
                    for (Iterator j = domains.iterator(); j.hasNext();) {
                        BDDDomain d = (BDDDomain) j.next();
                        int jj = d.getIndex();
                        if (Arrays.binarySearch(b, jj) < 0) {
                            dos.writeBytes("* ");
                            t.andWith(d.domain());
                        } else {
                            dos.writeBytes(v[jj] + " ");
                            t.andWith(d.ithVar(v[jj]));
                        }
                    }
                    q.applyWith(t, BDDFactory.diff);
                    dos.writeBytes("\n");
                    ++lines;
                }
                q.free();
            }
            System.out.println("Done writing " + lines + " lines.");
        } finally {
            if (dos != null) dos.close();
        }
    }

    /**
     * @param relation
     * @return
     */
    public String activeDomains(BDD relation) {
        BDD s = relation.support();
        int[] a = s.scanSetDomains();
        s.free();
        if (a == null) return "(none)";
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < a.length; ++i) {
            sb.append(solver.bdd.getDomain(a[i]));
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
    static class MyTupleIterator extends TupleIterator {
        Iterator i;
        List domains;

        MyTupleIterator(Iterator i, List domains) {
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
     * @return
     */
    public BDD getBDD() {
        return relation;
    }

    /**
     * @param b
     */
    public void setBDD(BDD b) {
        if (relation != null) relation.free();
        relation = b;
    }

    /**
     * @param i
     * @return
     */
    public BDDDomain getBDDDomain(int i) {
        return (BDDDomain) domains.get(i);
    }

    /**
     * @param a
     * @return
     */
    public BDDDomain getBDDDomain(Attribute a) {
        int i = attributes.indexOf(a);
        if (i == -1) return null;
        return (BDDDomain) domains.get(i);
    }

    /**
     * @return
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