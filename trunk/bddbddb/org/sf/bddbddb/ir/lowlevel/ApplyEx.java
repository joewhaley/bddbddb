// ApplyEx.java, created Jun 29, 2004 12:25:51 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.lowlevel;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.util.Pair;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;
import org.sf.javabdd.BDDFactory.BDDOp;

/**
 * ApplyEx
 * 
 * @author jwhaley
 * @version $Id$
 */
public class ApplyEx extends LowLevelOperation {
    BDDRelation r0, r1, r2;
    BDDOp op;
    List/* <Attribute> */attributes;

    /**
     * @param r0
     * @param r1
     * @param r2
     */
    public ApplyEx(BDDRelation r0, BDDRelation r1, BDDOp op, BDDRelation r2) {
        this.r0 = r0;
        this.r1 = r1;
        this.r2 = r2;
        this.op = op;
        this.attributes = new LinkedList(r1.getAttributes());
        this.attributes.removeAll(r2.getAttributes());
        this.attributes.addAll(r2.getAttributes());
        this.attributes.removeAll(r0.getAttributes());
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperation#visit(org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor)
     */
    public Object visit(LowLevelOperationVisitor i) {
        return i.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#toString()
     */
    public String toString() {
        return r0.toString() + " = " + getExpressionString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getExpressionString()
     */
    public String getExpressionString() {
        String opName;
        if (op == BDDFactory.and) opName = "relprod";
        else opName = op.toString() + "Ex";
        return opName + "(" + r1.toString() + "," + r2.toString() + "," + attributes + ")";
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getRelationDest() {
        return r0;
    }

    /*
     * (non-Javadoc)
     * 
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

    /**
     * @return
     */
    public BDDOp getOp() {
        return op;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#replaceSrc(org.sf.bddbddb.Relation,
     *      org.sf.bddbddb.Relation)
     */
    public void replaceSrc(Relation r_old, Relation r_new) {
        if (r1 == r_old) r1 = (BDDRelation) r_new;
        if (r2 == r_old) r2 = (BDDRelation) r_new;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#setRelationDest(org.sf.bddbddb.Relation)
     */
    public void setRelationDest(Relation r0) {
        this.r0 = (BDDRelation) r0;
    }

    public Operation copy() {
        return new ApplyEx(r0, r1, op, r2);
    }
}