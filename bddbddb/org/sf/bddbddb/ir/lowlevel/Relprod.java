// Relprod.java, created Jun 29, 2004 12:25:51 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.lowlevel;

import java.util.Iterator;
import java.util.List;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.util.Pair;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;

/**
 * Relprod
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Relprod extends LowLevelOperation {

    BDDRelation r0, r1, r2;
    List/*<Attribute>*/ attributes;

    /**
     * @param r0
     * @param r1
     * @param r2
     */
    public Relprod(BDDRelation r0, BDDRelation r1, BDDRelation r2, List/*<Attribute>*/ attributes) {
        this.r0 = r0;
        this.r1 = r1;
        this.r2 = r2;
        this.attributes = attributes;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperation#visit(org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor)
     */
    public Object visit(LowLevelOperationVisitor i) {
        return i.visit(this);
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#toString()
     */
    public String toString() {
        return r0.toString()+" = relprod("+r1.toString()+","+r2.toString()+","+attributes+")";
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() {
        return r0;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return new Pair(r1, r2);
    }

    /**
     * @return Returns the source relation.
     */
    public Relation getSrc1() {
        return r1;
    }
    
    /**
     * @return Returns the source relation.
     */
    public Relation getSrc2() {
        return r2;
    }

    /**
     * @return
     */
    public BDD getProjectSet() {
        BDD b = r1.getBDD().getFactory().one();
        for (Iterator i = attributes.iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            BDDDomain d = r1.getBDDDomain(a);
            b.andWith(d.set());
        }
        return b;
    }

    
    /**
     * @return Returns the attributes.
     */
    public List getAttributes() {
        return attributes;
    }
}