// Project.java, created Jun 29, 2004 12:25:38 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.LinkedList;
import java.util.List;
import org.sf.bddbddb.Relation;

/**
 * Project
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Project extends Operation {
    
    Relation r0, r1;
    List/*<Attribute>*/ attributes;
    
    /**
     * @param r0
     * @param r1
     */
    public Project(Relation r0, Relation r1) {
        this.r0 = r0;
        this.r1 = r1;
        this.attributes = new LinkedList(r1.getAttributes());
        this.attributes.removeAll(r0.getAttributes());
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString()+" = project("+r1.toString()+","+attributes.toString()+")";
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
