// Invert.java, created Jul 1, 2004 11:04:17 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;

/**
 * Invert
 * 
 * @author John Whaley
 * @version $Id$
 */
public class Invert extends Operation {
    
    Relation r0, r1;
    
    /**
     * @param r0
     * @param r1
     */
    public Invert(Relation r0, Relation r1) {
        this.r0 = r0;
        this.r1 = r1;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.OperationVisitor)
     */
    public Object visit(OperationVisitor i) {
        return i.visit(this);
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#toString()
     */
    public String toString() {
        return r0.toString()+" = invert("+r1.toString()+")";
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
        return Collections.singletonList(r1);
    }
    
}
