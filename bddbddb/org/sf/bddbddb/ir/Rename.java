// Rename.java, created Jun 29, 2004 12:25:20 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.util.Pair;

/**
 * Rename
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Rename extends Operation {
    
    Relation r0, r1;
    List/*<Pair<Attribute>>*/ renames;
    
    /**
     * @param r0
     * @param r1
     */
    public Rename(Relation r0, Relation r1) {
        this.r0 = r0;
        this.r1 = r1;
        this.renames = new LinkedList();
        for (int i = 0; i < r0.numberOfAttributes(); ++i) {
            Attribute a0 = r0.getAttribute(i);
            Attribute a1 = r1.getAttribute(i);
            if (!a1.equals(a0)) {
                renames.add(new Pair(a1, a0));
            }
        }
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(r0.toString());
        sb.append(" = rename(");
        sb.append(r1.toString());
        for (Iterator i = renames.iterator(); i.hasNext(); ) {
            Pair p = (Pair) i.next();
            sb.append(',');
            sb.append(p.left.toString());
            sb.append("->");
            sb.append(p.right.toString());
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
}
