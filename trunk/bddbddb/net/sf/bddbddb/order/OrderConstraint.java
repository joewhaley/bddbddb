// OrderConstraint.java, created Oct 22, 2004 5:22:13 PM by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

import net.sf.bddbddb.Attribute;
import net.sf.bddbddb.InferenceRule;
import net.sf.bddbddb.Variable;
import net.sf.bddbddb.XMLFactory;
import org.jdom.Element;

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
    public abstract boolean obeyedBy(Order order);
    public abstract Element toXMLElement(InferenceRule ir);
    
    private static Element toXMLElement(Object o, InferenceRule ir) {
        if (o instanceof Variable) {
            return ((Variable) o).toXMLElement(ir);
        } else if (o instanceof Attribute) {
            return ((Attribute) o).toXMLElement();
        } else {
            return null;
        }
    }
    
    protected void addXMLContent(Element e, InferenceRule ir) {
        e.addContent(toXMLElement(a, ir));
        e.addContent(toXMLElement(b, ir));
    }
    
    protected static Object getElement(Element e, XMLFactory f) {
        if (e.getName().equals("variable"))
            return Variable.fromXMLElement(e, f);
        else if (e.getName().equals("attribute"))
            return Attribute.fromXMLElement(e, f);
        else
            return null;
    }
}
