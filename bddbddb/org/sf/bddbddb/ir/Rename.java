// Rename.java, created Jun 29, 2004 12:25:20 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Iterator;
import java.util.Map;
import org.sf.bddbddb.Relation;

/**
 * Rename
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Rename extends Operation {
    
    Relation r0, r1;
    Map/*<Pair,Attribute>*/ renames;
    
    /**
     * @param r0
     * @param r1
     */
    public Rename(Relation r0, Relation r1, Map/*<Pair,Attribute>*/ renames) {
        this.r0 = r0;
        this.r1 = r1;
        this.renames = renames;
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(r0.toString());
        sb.append(" = rename(");
        sb.append(r1.toString());
        for (Iterator i = renames.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry p = (Map.Entry) i.next();
            sb.append(',');
            sb.append(p.getKey().toString());
            sb.append("->");
            sb.append(p.getValue().toString());
        }
        sb.append(")");
        return sb.toString();
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
