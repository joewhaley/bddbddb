// Nop.java, created Jul 7, 2004 11:50:51 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.dynamic;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.Operation;

/**
 * No operation.
 * 
 * @author John Whaley
 * @version $Id$
 */
public class Nop extends DynamicOperation {
    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.dynamic.DynamicOperation#visit(org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor)
     */
    public Object visit(DynamicOperationVisitor i) {
        return i.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return getExpressionString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getRelationDest()
     */
    public Relation getRelationDest() {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.EMPTY_LIST;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getExpressionString()
     */
    public String getExpressionString() {
        return "nop" + Integer.toString(id);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#setRelationDest(org.sf.bddbddb.Relation)
     */
    public void setRelationDest(Relation dest) {
    }

    public Operation copy() {
        return new Nop();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#replaceSrc(org.sf.bddbddb.Relation,
     *      org.sf.bddbddb.Relation)
     */
    public void replaceSrc(Relation r_old, Relation r_new) {
    }
}
