// OrderConstraint.java, created Oct 22, 2004 5:22:13 PM by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

/**
 * OrderConstraint
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class OrderConstraint {
    Object a, b;
    
    protected OrderConstraint(Object a, Object b) {
        this.a = a;
        this.b = b;
    }
    
    public int hashCode() {
        return a.hashCode() ^ (b.hashCode() << 1);
    }
    
    public abstract boolean isOpposite(OrderConstraint that);
    public abstract OrderConstraint getOpposite();
    
}
