// BooleanOperation.java, created Jun 29, 2004 1:52:09 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import org.sf.bddbddb.Relation;

/**
 * BooleanOperation
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class BooleanOperation extends Operation {
    
    Relation r0, r1, r2;
    
    /**
     * @param r0
     * @param r1
     * @param r2
     */
    public BooleanOperation(Relation r0, Relation r1, Relation r2) {
        this.r0 = r0;
        this.r1 = r1;
        this.r2 = r2;
    }
    
    /**
     * @return
     */
    public abstract String getName();
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString()+" = "+getName()+"("+r1.toString()+","+r2.toString()+")";
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() { return r0; }
    
}