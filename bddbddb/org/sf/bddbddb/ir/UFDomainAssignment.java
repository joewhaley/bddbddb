// UFDomainAssignment.java, created Jul 11, 2004 12:59:33 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.BDDSolver;
import org.sf.bddbddb.Domain;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.Solver;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.LinearMap;
import org.sf.bddbddb.util.Pair;
import org.sf.bddbddb.util.UnionFind;
import org.sf.javabdd.BDDDomain;

/**
 * UFDomainAssignment
 * 
 * @author John Whaley
 * @version $Id$
 */
public class UFDomainAssignment extends DomainAssignment {
    UnionFind uf;
    List neq_constraints;
    Set usedDomains;
    
    /**
     * @param s
     */
    public UFDomainAssignment(Solver s) {
        super(s);
        uf = new UnionFind(4096);
        neq_constraints = new LinkedList();
        usedDomains = new HashSet();
        this.initialize();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.DomainAssignment#validAssignments(org.sf.bddbddb.Relation)
     */
    public double validAssignments(Relation r) {
        // TODO Auto-generated method stub
        return 1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.DomainAssignment#validAssignment(org.sf.bddbddb.Relation)
     */
    public Map validAssignment(Relation r) {
        // TODO Auto-generated method stub
        return null;
    }

    public void doAssignment() {
        BDDSolver s = (BDDSolver) solver;
        Map physicalDomains = new HashMap();
        for (Iterator i = s.getBDDDomains().keySet().iterator(); i.hasNext();) {
            Domain d = (Domain) i.next();
            for (Iterator j = s.getBDDDomains(d).iterator(); j.hasNext();) {
                BDDDomain b = (BDDDomain) j.next();
                Object rep = uf.find(b);
                physicalDomains.put(rep, b);
                if (TRACE) System.out.println("Domain " + b + " rep: " + rep);
            }
        }
        for (int i = 0; i < s.getNumberOfRelations(); ++i) {
            BDDRelation r = (BDDRelation) s.getRelation(i);
            List domAssign = new ArrayList(r.getAttributes().size());
            for (Iterator j = r.getAttributes().iterator(); j.hasNext();) {
                Attribute a = (Attribute) j.next();
                Pair p = new Pair(r, a);
                Object assignment = uf.find(p);
                if (TRACE) System.out.println(p + " rep = " + assignment);
                BDDDomain b = (BDDDomain) physicalDomains.get(assignment);
                if (b != null) {
                    // Bound to b.
                    if (TRACE) System.out.println(p + " already bound to " + b);
                } else {
                    // Choose a binding.
                    b = chooseBDDDomain(r, a);
                    usedDomains.add(b);
                    uf.union(p, b);
                    if (TRACE) System.out.println(p + ": binding to " + b);
                    Object rep = uf.find(b);
                    physicalDomains.put(rep, b);
                    if (TRACE) System.out.println("Domain " + b + " rep: " + rep);
                }
                domAssign.add(b);
            }
            if (TRACE) System.out.println("Relation " + r + " domains: " + domAssign);
            r.setDomainAssignment(domAssign);
        }
    }

    BDDDomain chooseBDDDomain(BDDRelation r, Attribute a) {
        // TODO: need to choose a binding intelligently.
        BDDSolver s = (BDDSolver) solver;
        Domain d = a.getDomain();
        Pair p = new Pair(r, a);
        for (Iterator i = s.getBDDDomains(d).iterator(); i.hasNext();) {
            BDDDomain b = (BDDDomain) i.next();
            if (forceEqual(p, b)) {
                return b;
            }
        }
        BDDDomain b = s.allocateBDDDomain(d);
        if (TRACE) System.out.println("Allocating new domain " + b);
        return b;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.DomainAssignment#forceDifferent(org.sf.bddbddb.Relation)
     */
    void forceDifferent(Relation r) {
        if (TRACE) System.out.println("Forcing attributes to be different for "+r);
        for (Iterator j = r.getAttributes().iterator(); j.hasNext();) {
            Attribute a1 = (Attribute) j.next();
            Pair p1 = new Pair(r, a1);
            for (Iterator k = r.getAttributes().iterator(); k.hasNext();) {
                Attribute a2 = (Attribute) k.next();
                if (a1 == a2) continue;
                if (a1.getDomain() != a2.getDomain()) continue;
                Object rep1 = uf.find(a1);
                Object rep2 = uf.find(a2);
                Assert._assert(rep1 != rep2);
                Pair p2 = new Pair(r, a2);
                Pair p = new Pair(p1, p2);
                if (neq_constraints.contains(p)) continue;
                if (neq_constraints.contains(new Pair(p2, p1))) continue;
                if (TRACE) System.out.println("New constraint: "+p);
                neq_constraints.add(p);
            }
        }
    }

    boolean forceNotEqual(Object a1, Object a2) {
        if (TRACE) System.out.println("Forcing " + a1 + " != " + a2);
        Object rep1 = uf.find(a1);
        Object rep2 = uf.find(a2);
        if (rep1 == rep2) {
            if (TRACE) System.out.println("Cannot force, " + a1 + " = " + a2);
            return false;
        }
        Pair p = new Pair(a1, a2);
        if (neq_constraints.contains(p) || neq_constraints.contains(new Pair(a2, a1))) {
            if (TRACE) System.out.println("Already " + a1 + " != " + a2);
            return true;
        }
        neq_constraints.add(p);
        return true;
    }

    boolean forceEqual(Object a1, Object a2) {
        if (TRACE) System.out.println("Forcing " + a1 + " = " + a2);
        Object rep_1 = uf.find(a1);
        Object rep_2 = uf.find(a2);
        if (rep_1 == rep_2) {
            // Already match.
            if (TRACE) System.out.println("Already " + a1 + " = " + a2);
            return true;
        }
        for (Iterator i = neq_constraints.iterator(); i.hasNext();) {
            Pair p = (Pair) i.next();
            Object repa = uf.find(p.left);
            Object repb = uf.find(p.right);
            Assert._assert(repa != repb);
            if (repa == rep_1 && repb == rep_2 || repa == rep_2 && repb == rep_1) {
                // Merging will cause these to be merged! Bad!
                if (TRACE) System.out.println("Cannot, would violate constraint " + p.left + " != " + p.right);
                return false;
            }
        }
        // Merging a1 and a2 is ok.
        uf.union(a1, a2);
        return true;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.DomainAssignment#forceEqual(org.sf.bddbddb.Relation,
     *      org.sf.bddbddb.Attribute, int)
     */
    boolean forceEqual(Relation r1, Attribute a1, int k) {
        Domain dom = a1.getDomain();
        BDDDomain d = ((BDDSolver) solver).getBDDDomain(dom, k);
        usedDomains.add(d);
        for (Iterator i = ((BDDSolver) solver).getBDDDomains(dom).iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (o == d) continue;
            forceNotEqual(d, o);
        }
        return forceEqual(new Pair(r1, a1), d);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.DomainAssignment#forceEqual(org.sf.bddbddb.Relation,
     *      org.sf.bddbddb.Attribute, org.sf.bddbddb.Relation,
     *      org.sf.bddbddb.Attribute, boolean)
     */
    boolean forceEqual(Relation r1, Attribute a1, Relation r2, Attribute a2, boolean equal) {
        if (equal) {
            return forceEqual(new Pair(r1, a1), new Pair(r2, a2));
        } else {
            return forceNotEqual(new Pair(r1, a1), new Pair(r2, a2));
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.DomainAssignment#allocNewRelation(org.sf.bddbddb.Relation)
     */
    Relation allocNewRelation(Relation old_r) {
        Relation r = old_r.copy();
        Map m = new LinearMap();
        for (Iterator j = r.getAttributes().iterator(); j.hasNext();) {
            Attribute a = (Attribute) j.next();
            domainToAttributes.add(a.getDomain(), a);
        }
        forceDifferent(r);
        r.initialize();
        return r;
    }
}