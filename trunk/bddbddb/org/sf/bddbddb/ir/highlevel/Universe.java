// Universe.java, created Jul 1, 2004 11:01:59 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.highlevel;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;

/**
 * Universe
 * 
 * @author John Whaley
 * @version $Id$
 */
public class Universe extends HighLevelOperation {
    Relation r0;

    /**
     * @param r0
     */
    public Universe(Relation r0) {
        super();
        this.r0 = r0;
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
        return r0.toString() + " = universe()";
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getExpressionString()
     */
    public String getExpressionString() {
        return "universe()";
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
        return Collections.EMPTY_LIST;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#replaceSrc(org.sf.bddbddb.Relation, org.sf.bddbddb.Relation)
     */
    public void replaceSrc(Relation r_old, Relation r_new) {
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#setRelationDest(org.sf.bddbddb.Relation)
     */
    public void setRelationDest(Relation r0) {
        this.r0 = r0;
    }
}