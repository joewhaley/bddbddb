// Free.java, created Jul 1, 2004 12:42:19 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;

/**
 * Free
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Free extends Operation {
    
    Relation r;
    
    /**
     * @param r
     */
    public Free(Relation r) {
        this.r = r;
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.OperationVisitor)
     */
    public Object visit(OperationVisitor i) {
        return i.visit(this);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return "free("+r.toString()+")";
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() { return r; }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.singletonList(r);
    }
}
