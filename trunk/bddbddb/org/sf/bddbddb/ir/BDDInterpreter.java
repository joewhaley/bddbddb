// BDDInterpreter.java, created Jun 29, 2004 12:54:42 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Iterator;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.util.Assert;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;
import org.sf.javabdd.BDDPairing;

/**
 * BDDInterpreter
 * 
 * @author jwhaley
 * @version $Id$
 */
public class BDDInterpreter extends Interpreter {
    
    boolean TRACE = System.getProperty("traceinterpreter") != null;
    
    protected BDD makeDomainsMatch(BDD b, BDDRelation r1, BDDRelation r2) {
        boolean any = false;
        BDDPairing pair = b.getFactory().makePair();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext(); ) {
            Attribute a = (Attribute) i.next();
            BDDDomain d1 = r1.getBDDDomain(a);
            BDDDomain d2 = r2.getBDDDomain(a);
            if (d2 == null || d1 == d2) continue;
            any = true;
            pair.set(d1, d2);
            if (TRACE) System.out.println("   Renaming "+d1+" to "+d2);
        }
        if (any) {
            b.replaceWith(pair);
        }
        pair.reset();
        return b;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Join)
     */
    public Object perform(Join op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDDRelation r2 = (BDDRelation) op.r2;
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        BDD b2 = makeDomainsMatch(r2.getBDD().id(), r2, r0);
        if (TRACE) System.out.println("   And "+r1+","+r2);
        b1.andWith(b2);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: "+b1.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Project)
     */
    public Object perform(Project op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDD b = r1.getBDD().getFactory().one();
        for (Iterator i = op.attributes.iterator(); i.hasNext(); ) {
            Attribute a = (Attribute) i.next();
            BDDDomain d = r1.getBDDDomain(a);
            b.andWith(d.set());
            if (TRACE) System.out.println("   Projecting "+d);
        }
        if (TRACE) System.out.println("   Exist "+r1);
        BDD r = r1.getBDD().exist(b);
        b.free();
        BDD b1 = makeDomainsMatch(r, r1, r0);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: "+b1.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Rename)
     */
    public Object perform(Rename op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        boolean any = false;
        BDDPairing pair = r0.getBDD().getFactory().makePair();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext(); ) {
            Attribute a1 = (Attribute) i.next();
            BDDDomain d1 = r1.getBDDDomain(a1);
            Attribute a0 = (Attribute) op.renames.get(a1);
            if (a0 == null) a0 = a1;
            BDDDomain d0 = r0.getBDDDomain(a0);
            Assert._assert(d0 != null);
            if (d1.equals(d0)) continue;
            any = true;
            pair.set(d1, d0);
            if (TRACE) System.out.println("   Renaming "+d1+" to "+d0);
        }
        BDD b = r1.getBDD().id();
        if (any) {
            if (TRACE) System.out.println("   Replace "+r1);
            b.replaceWith(pair);
        }
        pair.reset();
        r0.setBDD(b);
        if (TRACE) System.out.println("   ---> Nodes: "+b.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Union)
     */
    public Object perform(Union op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDDRelation r2 = (BDDRelation) op.r2;
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        BDD b2 = makeDomainsMatch(r2.getBDD().id(), r2, r0);
        if (TRACE) System.out.println("   Or "+r1+","+r2);
        b1.orWith(b2);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: "+b1.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Difference)
     */
    public Object perform(Difference op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDDRelation r2 = (BDDRelation) op.r2;
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        BDD b2 = makeDomainsMatch(r2.getBDD().id(), r2, r0);
        if (TRACE) System.out.println("   Diff "+r1+","+r2);
        b1.applyWith(b2, BDDFactory.diff);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: "+b1.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.JoinConstant)
     */
    public Object perform(JoinConstant op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDD r = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        if (TRACE) System.out.println("   And "+r1+","+r0.getBDDDomain(op.a)+":"+op.value);
        r.andWith(r0.getBDDDomain(op.a).ithVar(op.value));
        r0.setBDD(r);
        if (TRACE) System.out.println("   ---> Nodes: "+r.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.GenConstant)
     */
    public Object perform(GenConstant op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        if (TRACE) System.out.println("   Ithvar "+r0.getBDDDomain(op.a)+":"+op.value);
        BDD r = r0.getBDDDomain(op.a).ithVar(op.value);
        r0.setBDD(r);
        if (TRACE) System.out.println("   ---> Nodes: "+r.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Free)
     */
    public Object perform(Free op) {
        BDDRelation r = (BDDRelation) op.r;
        if (TRACE) System.out.println("   Free "+r);
        r.free();
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Zero)
     */
    public Object perform(Zero op) {
        BDDRelation r = (BDDRelation) op.r;
        BDD b = r.getBDD().getFactory().zero();
        if (TRACE) System.out.println("   Zero "+r);
        r.setBDD(b);
        if (TRACE) System.out.println("   ---> Nodes: "+b.nodeCount());
        return null;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Universe)
     */
    public Object perform(Universe op) {
        BDDRelation r = (BDDRelation) op.r;
        BDD b = r.getBDD().getFactory().one();
        for (Iterator i = r.getAttributes().iterator(); i.hasNext(); ) {
            Attribute a = (Attribute) i.next();
            BDDDomain d = r.getBDDDomain(a);
            b.andWith(d.domain());
        }
        if (TRACE) System.out.println("   Domain "+r);
        r.setBDD(b);
        if (TRACE) System.out.println("   ---> Nodes: "+b.nodeCount());
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Invert)
     */
    public Object perform(Invert op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        if (TRACE) System.out.println("   Not "+r1);
        BDD r = makeDomainsMatch(r1.getBDD().not(), r1, r0);
        r0.setBDD(r);
        if (TRACE) System.out.println("   ---> Nodes: "+r.nodeCount());
        return null;
    }

}
