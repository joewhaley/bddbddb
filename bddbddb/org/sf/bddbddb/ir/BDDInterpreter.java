// BDDInterpreter.java, created Jun 29, 2004 12:54:42 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

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
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Join)
     */
    public Object perform(Join op) {
        // TODO Auto-generated method stub
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Project)
     */
    public Object perform(Project op) {
        // TODO Auto-generated method stub
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Rename)
     */
    public Object perform(Rename op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDDPairing p = r0.getBDD().getFactory().makePair();
        for (int i = 0; i < r0.numberOfAttributes(); ++i) {
            BDDDomain d0 = r0.getBDDDomain(i);
            BDDDomain d1 = r1.getBDDDomain(i);
            if (!d0.equals(d1)) {
                p.set(d0, d1);
            }
        }
        BDD r = r1.getBDD().replace(p);
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
        BDD r = r1.getBDD().or(r2.getBDD());
        r0.setBDD(r);
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.Difference)
     */
    public Object perform(Difference op) {
        BDDRelation r0 = (BDDRelation) op.r0;
        BDDRelation r1 = (BDDRelation) op.r1;
        BDDRelation r2 = (BDDRelation) op.r2;
        BDD r = r1.getBDD().apply(r2.getBDD(), BDDFactory.diff);
        r0.setBDD(r);
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.JoinConstant)
     */
    public Object perform(JoinConstant op) {
        // TODO Auto-generated method stub
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Interpreter#perform(org.sf.bddbddb.ir.GenConstant)
     */
    public Object perform(GenConstant op) {
        // TODO Auto-generated method stub
        return null;
    }
    
}
