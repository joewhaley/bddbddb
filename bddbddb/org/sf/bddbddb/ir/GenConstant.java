// GenConstant.java, created Jun 29, 2004 2:57:29 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.Relation;

/**
 * GenConstant
 * 
 * @author jwhaley
 * @version $Id$
 */
public class GenConstant extends Operation {
    
    Relation r0;
    Attribute a;
    long value;
    
    /**
     * @param r0
     * @param a
     * @param value
     */
    public GenConstant(Relation r0, Attribute a, long value) {
        this.r0 = r0;
        this.a = a;
        this.value = value;
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString()+" = const("+a.toString()+"="+value+")";
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#perform(org.sf.bddbddb.ir.Interpreter)
     */
    public Object perform(Interpreter i) {
        return i.perform(this);
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() { return r0; }
}
