// Zero.java, created Jul 1, 2004 11:10:38 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import org.sf.bddbddb.Relation;

/**
 * Zero
 * 
 * @author John Whaley
 * @version $Id$
 */
public class Zero extends Operation {
    
    Relation r;
    
    /**
     * @param r
     */
    public Zero(Relation r) {
        this.r = r;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#perform(org.sf.bddbddb.ir.Interpreter)
     */
    public Object perform(Interpreter i) {
        return i.perform(this);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r.toString()+" = zero()";
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() {
        return r;
    }
}
