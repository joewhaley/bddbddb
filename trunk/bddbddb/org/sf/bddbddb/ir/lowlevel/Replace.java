// Replace.java, created Jul 12, 2004 1:34:38 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.lowlevel;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.Operation;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;
import org.sf.javabdd.BDDPairing;

/**
 * Replace
 * 
 * @author John Whaley
 * @version $Id$
 */
public class Replace extends LowLevelOperation {
    BDDRelation r0, r1;

    /**
     * @param r0
     * @param r1
     */
    public Replace(BDDRelation r0, BDDRelation r1) {
        this.r0 = r0;
        this.r1 = r1;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperation#visit(org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor)
     */
    public Object visit(LowLevelOperationVisitor i) {
        return i.visit(this);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString()+" = "+getExpressionString();
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getRelationDest()
     */
    public Relation getRelationDest() {
        return r0;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#setRelationDest(org.sf.bddbddb.Relation)
     */
    public void setRelationDest(Relation r0) {
        this.r0 = (BDDRelation) r0;
    }

    /**
     * @return
     */
    public BDDRelation getSrc() {
        return r1;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.singletonList(r1);
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#replaceSrc(org.sf.bddbddb.Relation, org.sf.bddbddb.Relation)
     */
    public void replaceSrc(Relation r_old, Relation r_new) {
        if (r1 == r_old) r1 = (BDDRelation) r_new;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getExpressionString()
     */
    public String getExpressionString() {
        return "replace("+r1.toString()+Operation.getRenames(r1,r0)+")";
    }
    
    /**
     * @return
     */
    public BDDPairing getPairing(BDDFactory factory) {
        boolean any = false;
        BDDPairing pair = factory.makePair();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            BDDDomain d1 = r1.getBDDDomain(a);
            BDDDomain d2 = r0.getBDDDomain(a);
            if (d2 == null || d1 == d2) continue;
            any = true;
            pair.set(d1, d2);
        }
        if (any)
            return pair;
        else 
            return null;
    }
}