// Save.java, created Jul 3, 2004 12:54:37 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.highlevel;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;

/**
 * Save
 * 
 * @author John Whaley
 * @version $Id$
 */
public class Save extends HighLevelOperation {
    Relation r;

    /**
     * @param r
     */
    public Save(Relation r) {
        super();
        this.r = r;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.HighLevelOperationVisitor)
     */
    public Object visit(HighLevelOperationVisitor i) {
        return i.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return "save(" + r.toString() + ")";
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getExpressionString()
     */
    public String getExpressionString() {
        return toString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.singletonList(r);
    }

    /**
     * @return Returns the source relation.
     */
    public Relation getSrc() {
        return r;
    }
}