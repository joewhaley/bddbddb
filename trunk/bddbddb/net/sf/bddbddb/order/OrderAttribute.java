// OrderAttribute.java, created Oct 28, 2004 6:11:41 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

import net.sf.bddbddb.order.OrderConstraint.AfterConstraint;
import net.sf.bddbddb.order.OrderConstraint.BeforeConstraint;
import net.sf.bddbddb.order.OrderConstraint.InterleaveConstraint;
import weka.core.FastVector;

/**
 * OrderAttribute
 * 
 * @author jwhaley
 * @version $Id$
 */
public class OrderAttribute extends weka.core.Attribute {
    Object a, b;
    
    static FastVector my_nominal_values = new FastVector(3);
    static {
        my_nominal_values.addElement("<");
        my_nominal_values.addElement("~");
        my_nominal_values.addElement(">"); 
    }
    
    public static OrderAttribute makeOrderAttribute(OrderConstraint c) {
        return new OrderAttribute(c.a, c.b);
    }
    
    public static OrderAttribute makeOrderAttribute(Object a, Object b) {
        if (OrderConstraint.compare(a, b)) {
            return new OrderAttribute(a, b);
        } else {
            return new OrderAttribute(b, a);
        }
    }
    
    private OrderAttribute(Object a, Object b) {
        super(a+","+b, my_nominal_values);
    }
    
    public OrderConstraint getConstraint(weka.core.Instance i) {
        int k = (int) i.value(this);
        switch (k) {
            case 0: return OrderConstraint.makePrecedenceConstraint(a, b);
            case 1: return OrderConstraint.makePrecedenceConstraint(b, a);
            case 2: return OrderConstraint.makeInterleaveConstraint(a, b);
            default: return null;
        }
    }

    public static int getType(OrderConstraint oc) {
        if (oc instanceof BeforeConstraint) return 0;
        else if (oc instanceof InterleaveConstraint) return 1;
        else if (oc instanceof AfterConstraint) return 2;
        else return -1;
    }
    
}
