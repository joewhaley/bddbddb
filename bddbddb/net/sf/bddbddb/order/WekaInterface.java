// WekaInterface.java, created Oct 31, 2004 1:17:46 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import net.sf.bddbddb.Attribute;
import net.sf.bddbddb.InferenceRule;
import net.sf.bddbddb.Variable;
import net.sf.bddbddb.order.OrderConstraint.AfterConstraint;
import net.sf.bddbddb.order.OrderConstraint.BeforeConstraint;
import net.sf.bddbddb.order.OrderConstraint.InterleaveConstraint;
import weka.core.FastVector;
import weka.core.Instance;
import weka.core.Instances;

/**
 * WekaInterface
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class WekaInterface {
    
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
    
    public static int getType(OrderConstraint oc) {
        if (oc instanceof BeforeConstraint) return 0;
        else if (oc instanceof InterleaveConstraint) return 1;
        else if (oc instanceof AfterConstraint) return 2;
        else return -1;
    }
    
    public static class OrderAttribute extends weka.core.Attribute {
        Object a, b;
        
        static FastVector my_nominal_values = new FastVector(3);
        static {
            my_nominal_values.addElement("<");
            my_nominal_values.addElement("~");
            my_nominal_values.addElement(">"); 
        }
        
        private OrderAttribute(Object a, Object b) {
            super(a+","+b, my_nominal_values);
            this.a = a;
            this.b = b;
        }
        
        public OrderConstraint getConstraint(int k) {
            switch (k) {
                case 0: return OrderConstraint.makePrecedenceConstraint(a, b);
                case 1: return OrderConstraint.makeInterleaveConstraint(a, b);
                case 2: return OrderConstraint.makePrecedenceConstraint(b, a);
                default: return null;
            }
        }
        
        public OrderConstraint getConstraint(weka.core.Instance i) {
            int k = (int) i.value(this);
            return getConstraint(k);
        }

    }
    
    public static void addAllPairs(FastVector v, Collection c) {
        for (Iterator i = c.iterator(); i.hasNext(); ) {
            Object a = i.next();
            Iterator j = c.iterator();
            while (j.hasNext() && j.next() != a) ;
            while (j.hasNext()) {
                Object b = j.next();
                OrderAttribute oa = makeOrderAttribute(a, b);
                v.addElement(oa);
            }
        }
    }

    public static FastVector constructVarAttributes(Collection vars) {
        FastVector v = new FastVector();
        addAllPairs(v, vars);
        return v;
    }
    
    public static FastVector constructAttribAttributes(InferenceRule ir, Collection vars) {
        Collection attribs = new LinkedList();
        for (Iterator i = vars.iterator(); i.hasNext(); ) {
            Variable v = (Variable) i.next();
            Attribute a = ir.getAttribute(v);
            if (a != null) attribs.add(a);
        }
        FastVector v = new FastVector();
        addAllPairs(v, attribs);
        return v;
    }
    
    public static FastVector constructDomainAttributes(InferenceRule ir, Collection vars) {
        Collection domains = new LinkedList();
        for (Iterator i = vars.iterator(); i.hasNext(); ) {
            Variable v = (Variable) i.next();
            Attribute a = ir.getAttribute(v);
            if (a != null) domains.add(a.getDomain());
        }
        FastVector v = new FastVector();
        addAllPairs(v, domains);
        return v;
    }
    
    public static class OrderInstance extends Instance {
        
        public static OrderInstance construct(Order o, Instances dataSet) {
            return construct(o, dataSet, 1);
        }
        
        public static OrderInstance construct(Order o, Instances dataSet, double weight) {
            double[] d = new double[dataSet.numAttributes()];
            for (int i = 0; i < d.length; ++i) {
                d[i] = Instance.missingValue();
            }
            for (Iterator i = o.getConstraints().iterator(); i.hasNext(); ) {
                OrderConstraint oc = (OrderConstraint) i.next();
                // TODO: use a map from Pair to int instead of building String and doing linear search.
                String cName = oc.getFirst()+","+oc.getSecond();
                OrderAttribute oa = (OrderAttribute) dataSet.attribute(cName);
                if (oa != null) {
                    d[oa.index()] = getType(oc);
                } else {
                    System.out.println("Warning: cannot find constraint "+oc+" in set "+dataSet);
                }
            }
            return new OrderInstance(weight, d, o);
        }
        
        protected Order o;
        
        protected OrderInstance(double w, double[] d, Order o) {
            super(w, d);
            this.o = o;
        }
        protected OrderInstance(OrderInstance that) {
            super(that);
            this.o = that.o;
        }
        
        public Object copy() {
            return new OrderInstance(this);
        }
        
        public Order getOrder() {
            return o;
        }
        
    }

}
