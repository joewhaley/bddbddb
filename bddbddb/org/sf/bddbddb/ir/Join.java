// Join.java, created Jun 29, 2004 12:25:51 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.LinkedList;
import java.util.List;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.util.Pair;

/**
 * Join
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Join extends Operation {
    
    Relation r0, r1, r2;
    List/*<Attribute>*/ attributes;
    
    /**
     * @param r0
     * @param r1
     * @param r2
     */
    public Join(Relation r0, Relation r1, Relation r2) {
        this.r0 = r0;
        this.r1 = r1;
        this.r2 = r2;
        this.attributes = new LinkedList();
        this.attributes.addAll(r1.getAttributes());
        this.attributes.retainAll(r2.getAttributes());
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString()+" = join("+r1.toString()+","+r2.toString()+")";
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
        return new Pair(r1, r2);
    }
}
