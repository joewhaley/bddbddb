// Operation.java, created Jun 29, 2004 12:24:59 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Iterator;
import java.util.List;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.IterationElement;
import org.sf.bddbddb.Relation;
import org.sf.javabdd.BDDDomain;

/**
 * Operation
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Operation implements IterationElement {
    static int opNumber = 0;

    /**
     * @return the number of operations generated so far
     */
    public static int getNumberOfOperations() {
        return opNumber + 1;
    }
    
    /**
     * Unique ID number for this operation.
     */
    public final int id;

    /**
     *  
     */
    public Operation() {
        id = ++opNumber;
    }

    /**
     * @param i
     * @return the result of the visit
     */
    public abstract Object visit(OperationVisitor i);

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public abstract String toString();

    /**
     * @return the destination relation of this operation, or null
     */
    public abstract Relation getRelationDest();

    /**
     * @param r0
     */
    public abstract void setRelationDest(Relation r0);

    /**
     * @return the source relation of this operation
     */
    public abstract List/*<Relation>*/ getSrcs();

    /**
     * @param r_old
     * @param r_new
     */
    public abstract void replaceSrc(Relation r_old, Relation r_new);

    /**
     * @return the expression in string form
     */
    public abstract String getExpressionString();

    public abstract Operation copy();

    public static String getRenames(BDDRelation r1, BDDRelation r2) {
        StringBuffer sb = new StringBuffer();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            BDDDomain d1 = r1.getBDDDomain(a);
            BDDDomain d2 = r2.getBDDDomain(a);
            if (d2 == null || d1 == d2) continue;
            sb.append("," + d1 + "->" + d2);
        }
        return sb.toString();
    }
}