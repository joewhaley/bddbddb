// BDDInterpreter.java, created Jun 29, 2004 12:54:42 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Iterator;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
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
    
    boolean TRACE = true;
    
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
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        if (TRACE) System.out.println("   Exist "+r1);
        BDD r = b1.exist(b);
        b.free(); b1.free();
        r0.setBDD(r);
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Rename)
     */
    public Object perform(Rename op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDDPairing p = r0.getBDD().getFactory().makePair();
        // Attributes must be in the same order.
        boolean any = false;
        for (int i = 0; i < r0.numberOfAttributes(); ++i) {
            BDDDomain d0 = r0.getBDDDomain(i);
            BDDDomain d1 = r1.getBDDDomain(i);
            if (!d0.equals(d1)) {
                any = true;
                p.set(d1, d0);
                if (TRACE) System.out.println("   Renaming "+d1+" to "+d0);
            }
        }
        BDD r;
        if (any) {
            if (TRACE) System.out.println("   Replace "+r1);
            r = r1.getBDD().replace(p);
        } else {
            r = r1.getBDD().id();
        }
        r0.setBDD(r);
        p.reset();
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
    
}
