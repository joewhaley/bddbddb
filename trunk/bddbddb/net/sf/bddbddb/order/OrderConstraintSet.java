// OrderConstraintSet.java, created Oct 27, 2004 11:51:27 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.StringTokenizer;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import jwutil.collections.GenericMultiMap;
import jwutil.collections.MultiMap;
import net.sf.bddbddb.order.OrderConstraint.AfterConstraint;
import net.sf.bddbddb.order.OrderConstraint.BeforeConstraint;
import net.sf.bddbddb.order.OrderConstraint.InterleaveConstraint;

/**
 * OrderConstraintSet
 * 
 * @author jwhaley
 * @version $Id$
 */
public class OrderConstraintSet {
    
    LinkedHashSet set;
    MultiMap objToConstraints;
    
    /**
     * 
     */
    public OrderConstraintSet() {
        set = new LinkedHashSet();
        objToConstraints = new GenericMultiMap();
    }
    
    public boolean constrain(OrderConstraint c) {
        if (set.contains(c)) return true;
        if (set.contains(c.getOpposite1())) return false;
        if (set.contains(c.getOpposite2())) return false;
        if (c instanceof InterleaveConstraint) addInterleaveConstraint(c);
        else addPrecedenceConstraint(c);
        return true;
    }
    
    void checkTransitivePrecedence(Object a, Object b, Object c, Object d) {
        if (b.equals(c)) {
            addPrecedenceConstraint(a, d);
        } else if (a.equals(d)) {
            addPrecedenceConstraint(c, b);
        }
    }
    
    void addInterleaveConstraint(Object a, Object b) {
        if (a.equals(b)) return;
        OrderConstraint o = OrderConstraint.makeInterleaveConstraint(a, b);
        addInterleaveConstraint(o);
    }
    void addInterleaveConstraint(OrderConstraint c) {
        if (set.contains(c)) return;
        set.add(c);
        Collection c1 = objToConstraints.getValues(c.a);
        Collection c2 = objToConstraints.getValues(c.b);
        objToConstraints.add(c.a, c);
        objToConstraints.add(c.b, c);
        addInterleaveConstraints(c.a, c.b, c1);
        addInterleaveConstraints(c.a, c.b, c2);
    }
    void addInterleaveConstraints(Object a, Object b, Collection ocs) {
        for (Iterator i = ocs.iterator(); i.hasNext(); ) {
            OrderConstraint oc = (OrderConstraint) i.next();
            if (oc instanceof InterleaveConstraint) {
                addInterleaveConstraint(a, oc.a);
                addInterleaveConstraint(a, oc.b);
                addInterleaveConstraint(b, oc.a);
                addInterleaveConstraint(b, oc.b);
            } else {
                Object c, d;
                if (oc instanceof BeforeConstraint) {
                    c = oc.a; d = oc.b;
                } else {
                    c = oc.b; d = oc.a;
                }
                checkTransitivePrecedence(a, b, c, d);
                checkTransitivePrecedence(b, a, c, d);
            }
        }
    }
    
    void addPrecedenceConstraint(Object a, Object b) {
        OrderConstraint o = OrderConstraint.makePrecedenceConstraint(a, b);
        addPrecedenceConstraint(o);
    }
    void addPrecedenceConstraint(OrderConstraint c) {
        if (set.contains(c)) return;
        set.add(c);
        Collection c1 = objToConstraints.getValues(c.a);
        Collection c2 = objToConstraints.getValues(c.b);
        objToConstraints.add(c.a, c);
        objToConstraints.add(c.b, c);
        if (c instanceof BeforeConstraint) {
            addPrecedenceConstraints(c.a, c.b, c1);
            addPrecedenceConstraints(c.a, c.b, c2);
        } else {
            addPrecedenceConstraints(c.b, c.a, c1);
            addPrecedenceConstraints(c.b, c.a, c2);
        }
    }
    void addPrecedenceConstraints(Object a, Object b, Collection ocs) {
        for (Iterator i = ocs.iterator(); i.hasNext(); ) {
            OrderConstraint oc = (OrderConstraint) i.next();
            Object c, d;
            if (oc instanceof AfterConstraint) {
                c = oc.b; d = oc.a;
            } else {
                c = oc.a; d = oc.b;
                if (oc instanceof InterleaveConstraint)
                    checkTransitivePrecedence(a, b, d, c);
            }
            checkTransitivePrecedence(a, b, c, d);
        }
    }
    
    public Object findEarliest(Object o) {
        return findEarliest(o, null);
    }
    public Object findEarliest(Object o, Set skip) {
        Collection c = objToConstraints.getValues(o);
        if (c != null) {
            for (Iterator i = c.iterator(); i.hasNext(); ) {
                OrderConstraint oc = (OrderConstraint) i.next();
                if (oc instanceof BeforeConstraint) {
                    if (o.equals(oc.b) &&
                        (skip == null || !skip.contains(oc.a))) {
                        return findEarliest(oc.a, skip);
                    }
                } else if (oc instanceof AfterConstraint) {
                    if (o.equals(oc.a) &&
                        (skip == null || !skip.contains(oc.b))) {
                        return findEarliest(oc.b, skip);
                    }
                }
            }
        }
        return o;
    }
    
    Collection getInterleaved(Object o) {
        Collection result = new LinkedList();
        result.add(o);
        Collection c = objToConstraints.getValues(o);
        if (c != null) {
            for (Iterator i = c.iterator(); i.hasNext(); ) {
                OrderConstraint oc = (OrderConstraint) i.next();
                if (oc instanceof InterleaveConstraint) {
                    if (o.equals(oc.a)) result.add(oc.b);
                    else result.add(oc.a);
                }
            }
        }
        return result;
    }
    
    public Order generateOrder(Collection vars) {
        Set done = new HashSet(vars.size());
        List result = new ArrayList(vars.size());
        for (Iterator i = vars.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (done.contains(o)) continue;
            o = findEarliest(o, done);
            Collection c = getInterleaved(o);
            if (c.size() == 1) result.add(c.iterator().next());
            else result.add(c);
            done.addAll(c);
        }
        Order o = new Order(result);
        return o;
    }
    
    public String toString() {
        return set.toString();
    }
    
    public static void main(String[] args) {
        OrderConstraintSet dis = new OrderConstraintSet();
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        Set allStrings = new HashSet();
        try {
            for (;;) {
                System.out.print("Enter constraint: ");
                String s = in.readLine();
                if (s == null) break;
                if (s.equals("done")) break;
                StringTokenizer st = new StringTokenizer(s, "<>~", true);
                String a = st.nextToken();
                String op = st.nextToken();
                String b = st.nextToken();
                OrderConstraint c;
                if (op.equals("<")) c = OrderConstraint.makePrecedenceConstraint(a, b);
                else if (op.equals(">")) c = OrderConstraint.makePrecedenceConstraint(b, a);
                else if (op.equals("~")) c = OrderConstraint.makeInterleaveConstraint(a, b);
                else {
                    continue;
                }
                if (dis.constrain(c)) {
                    System.out.println("Constraints now: "+dis);
                } else {
                    System.out.println("Cannot add constraint!");
                }
                allStrings.add(a);
                allStrings.add(b);
            }
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        Order o = dis.generateOrder(allStrings);
        System.out.println("Final order is: "+o);
    }
}
