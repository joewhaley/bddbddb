// NotInterleaveConstraint.java, created Oct 22, 2004 5:23:57 PM by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

/**
 * NotInterleaveConstraint
 * 
 * @author jwhaley
 * @version $Id$
 */
public class NotInterleaveConstraint extends OrderConstraint {
    
    public NotInterleaveConstraint(Object a, Object b) {
        super(a, b);
    }
    
    public boolean equals(NotInterleaveConstraint that) {
        return
            this.a.equals(that.a) && this.b.equals(that.b) ||
            this.a.equals(that.b) && this.b.equals(that.a);
    }
    
    public boolean equals(Object o) {
        if (o instanceof NotInterleaveConstraint)
            return equals((NotInterleaveConstraint) o);
        else
            return false;
    }
    
    public String toString() {
        return a+"!~"+b;
    }
    
    public boolean isOpposite(InterleaveConstraint that) {
        return
            this.a.equals(that.a) && this.b.equals(that.b) ||
            this.a.equals(that.b) && this.b.equals(that.a);
    }
    
    public boolean isOpposite(OrderConstraint that) {
        if (that instanceof InterleaveConstraint)
            return equals((InterleaveConstraint) that);
        else
            return false;
    }
    
    public OrderConstraint getOpposite() {
        return new InterleaveConstraint(a, b);
    }
}
