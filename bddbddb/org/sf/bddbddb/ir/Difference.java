// Difference.java, created Jun 29, 2004 1:35:00 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import org.sf.bddbddb.Relation;

/**
 * Difference
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Difference extends BooleanOperation {
    /**
     * @param r0
     * @param r1
     * @param r2
     */
    public Difference(Relation r0, Relation r1, Relation r2) {
        super(r0, r1, r2);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.BooleanOperation#getName()
     */
    public String getName() {
        return "diff";
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.OperationVisitor)
     */
    public Object visit(OperationVisitor i) {
        return i.visit(this);
    }
}