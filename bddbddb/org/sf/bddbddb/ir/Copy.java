// Copy.java, created Jul 2, 2004 12:28:31 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;

/**
 * Copy
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Copy extends Operation {
    Relation r0, r1;

    /**
     * @param r0
     * @param r1
     */
    public Copy(Relation r0, Relation r1) {
        super();
        this.r0 = r0;
        this.r1 = r1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.OperationVisitor)
     */
    public Object visit(OperationVisitor i) {
        return i.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString() + " = copy(" + r1.toString() + ")";
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() {
        return r0;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.singletonList(r1);
    }
}