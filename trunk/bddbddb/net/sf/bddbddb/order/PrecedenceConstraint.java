// PrecedenceConstraint.java, created Oct 22, 2004 5:22:49 PM by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

import net.sf.bddbddb.InferenceRule;
import net.sf.bddbddb.XMLFactory;
import org.jdom.Element;

/**
 * PrecedenceConstraint
 * 
 * @author jwhaley
 * @version $Id$
 */
public class PrecedenceConstraint extends OrderConstraint {
    
    public PrecedenceConstraint(Object a, Object b) {
        super(a, b);
    }
    
    public boolean equals(PrecedenceConstraint that) {
        return this.a.equals(that.a) && this.b.equals(that.b);
    }
    
    public boolean equals(Object o) {
        if (o instanceof PrecedenceConstraint)
            return equals((PrecedenceConstraint) o);
        else
            return false;
    }
    
    public String toString() {
        return a+"<"+b;
    }
    
    public boolean isOpposite(PrecedenceConstraint that) {
        return this.a.equals(that.b) && this.b.equals(that.a);
    }
    
    public boolean isOpposite(OrderConstraint that) {
        if (that instanceof PrecedenceConstraint)
            return equals((PrecedenceConstraint) that);
        else
            return false;
    }
    
    public OrderConstraint getOpposite() {
        return new PrecedenceConstraint(b, a);
    }
    
    public boolean obeyedBy(Order o) {
        return o.getConstraints().contains(this);
    }
    
    public static PrecedenceConstraint fromXMLElement(Element e, XMLFactory f) {
        Object a = getElement((Element) e.getContent(0), f);
        Object b = getElement((Element) e.getContent(1), f);
        return new PrecedenceConstraint(a, b);
    }
    
    public Element toXMLElement(InferenceRule ir) {
        Element e = new Element("precedenceConstraint");
        addXMLContent(e, ir);
        return e;
    }
}
