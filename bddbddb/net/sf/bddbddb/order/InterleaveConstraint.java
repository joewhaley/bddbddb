// InterleaveConstraint.java, created Oct 22, 2004 5:23:25 PM by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

import net.sf.bddbddb.InferenceRule;
import net.sf.bddbddb.XMLFactory;
import org.jdom.Element;

/**
 * InterleaveConstraint
 * 
 * @author jwhaley
 * @version $Id$
 */
public class InterleaveConstraint extends OrderConstraint {
    
    public InterleaveConstraint(Object a, Object b) {
        super(a, b);
    }
    
    public boolean equals(InterleaveConstraint that) {
        return
            this.a.equals(that.a) && this.b.equals(that.b) ||
            this.a.equals(that.b) && this.b.equals(that.a);
    }
    
    public boolean equals(Object o) {
        if (o instanceof InterleaveConstraint)
            return equals((InterleaveConstraint) o);
        else
            return false;
    }
    
    public String toString() {
        return a+"~"+b;
    }
    
    public boolean isOpposite(NotInterleaveConstraint that) {
        return
            this.a.equals(that.a) && this.b.equals(that.b) ||
            this.a.equals(that.b) && this.b.equals(that.a);
    }
    
    public boolean isOpposite(OrderConstraint that) {
        if (that instanceof NotInterleaveConstraint)
            return equals((NotInterleaveConstraint) that);
        else
            return false;
    }
    
    public OrderConstraint getOpposite() {
        return new NotInterleaveConstraint(a, b);
    }
    
    public boolean obeyedBy(Order o) {
        return o.getConstraints().contains(this);
    }

    public static InterleaveConstraint fromXMLElement(Element e, XMLFactory f) {
        Object a = getElement((Element) e.getContent(0), f);
        Object b = getElement((Element) e.getContent(1), f);
        return new InterleaveConstraint(a, b);
    }
    
    public Element toXMLElement(InferenceRule ir) {
        Element e = new Element("interleaveConstraint");
        addXMLContent(e, ir);
        return e;
    }
}
