// JoinConstant.java, created Jun 29, 2004 2:57:29 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.Relation;

/**
 * JoinConstant
 * 
 * @author jwhaley
 * @version $Id$
 */
public class JoinConstant extends Operation {
    
    Relation r0, r1;
    Attribute a;
    long value;
    
    /**
     * @param r0
     * @param r1
     * @param a
     * @param value
     */
    public JoinConstant(Relation r0, Relation r1, Attribute a, long value) {
        this.r0 = r0;
        this.r1 = r1;
        this.a = a;
        this.value = value;
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString()+" = restrict("+r1.toString()+","+a.toString()+"="+value+")";
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.OperationVisitor)
     */
    public Object visit(OperationVisitor i) {
        return i.visit(this);
    }
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getDest() { return r0; }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.singletonList(r1);
    }
}
