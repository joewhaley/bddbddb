// Union.java, created Jun 29, 2004 1:32:45 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import org.sf.bddbddb.Relation;

/**
 * Union
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Union extends BooleanOperation {
    
    /**
     * @param r0
     * @param r1
     * @param r2
     */
    public Union(Relation r0, Relation r1, Relation r2) {
        super(r0, r1, r2);
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.BooleanOperation#getName()
     */
    public String getName() {
        return "union";
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#perform(org.sf.bddbddb.ir.Interpreter)
     */
    public Object perform(Interpreter i) {
        return i.perform(this);
    }
}
