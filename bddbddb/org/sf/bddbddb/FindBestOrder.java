// FindBestOrder.java, created Aug 21, 2004 1:17:30 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.NoSuchElementException;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.PermutationGenerator;

/**
 * FindBestOrder
 * 
 * @author John Whaley
 * @version $Id$
 */
public class FindBestOrder {
    
    Map/*<Relation,OrderingInfo>*/ orderInfo;
    
    /**
     * 
     */
    public FindBestOrder() {
        super();
    }
    
    public static OrderIterator generateAllOrders(List vars) {
        return new OrderIterator(vars);
    }
    
    public static class OrderIterator implements Iterator {
        
        List orig;
        List current;
        PermutationGenerator g;
        int comboCounter = 0;
        
        public OrderIterator(List a) {
            orig = new ArrayList(a);
            gotoNextCombo();
        }
        
        public boolean hasNextCombo() {
            int elements = orig.size();
            return (comboCounter < (1 << (elements-1)));
        }
        
        public static List generateCombo(int bits, List l) {
            int elements = l.size();
            List result = new ArrayList(elements);
            Iterator i = l.iterator();
            boolean lastCombine = false;
            Object last = i.next();
            int k = bits;
            while (i.hasNext()) {
                Object o = i.next();
                boolean combine = (k & 1) == 1;
                if (combine) {
                    if (lastCombine) {
                        ((Collection) last).add(o);
                    } else {
                        List list = new ArrayList(elements);
                        list.add(last);
                        list.add(o);
                        last = list;
                    }
                } else {
                    result.add(last);
                    last = o;
                }
                lastCombine = combine;
                k >>>= 1;
            }
            result.add(last);
            return result;
        }
        
        public void gotoNextCombo() {
            if (!hasNextCombo()) {
                throw new NoSuchElementException();
            }
            current = generateCombo(comboCounter++, orig);
            int currentSize = current.size();
            if (currentSize > 0)
                g = new PermutationGenerator(currentSize);
            else
                g = null;
        }
        
        public boolean hasNext() {
            if (g != null && g.hasMore()) return true;
            return hasNextCombo();
        }

        public Object next() {
            return nextOrder();
        }
        
        public Order nextOrder() {
            if (g == null) {
                if (current == null) {
                    gotoNextCombo();
                } else {
                    List result = current;
                    current = null;
                    return new Order(result);
                }
            }
            if (!g.hasMore()) {
                gotoNextCombo();
                return nextOrder();
            }
            int[] a = g.getNext();
            List result = new ArrayList();
            for (int i = 0; i < a.length; ++i) {
                result.add(current.get(a[i]));
            }
            return new Order(result);
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
    
    public static class Order implements List {
        List list;
        
        public Order(List l) {
            this.list = l;
        }
        
        public Collection getFlattened() {
            Collection result = new LinkedList();
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                Object o = i.next();
                if (o instanceof Collection) {
                    result.addAll((Collection) o);
                } else {
                    result.add(o);
                }
            }
            return result;
        }
        
        private static Object intersect(Object a, Object b) {
            if (a instanceof Collection) {
                Collection ca = (Collection) a;
                if (b instanceof Collection) {
                    Collection result = new LinkedList();
                    result.addAll(ca);
                    result.retainAll((Collection) b);
                    if (result.isEmpty()) return null;
                    else if (result.size() == 1) return result.iterator().next();
                    else return result;
                }
                if (ca.contains(b)) return b;
            } else if (b instanceof Collection) {
                if (((Collection) b).contains(a)) return a;
            } else {
                if (a.equals(b)) return a;
            }
            return null;
        }
        
        static void addAllNew(Collection c, Collection c2) {
            outer:
            for (ListIterator c2i = ((List)c2).listIterator(); c2i.hasNext(); ) {
                List l2 = (List) c2i.next();
                for (ListIterator c1i = ((List)c).listIterator(); c1i.hasNext(); ) {
                    List l1 = (List) c1i.next();
                    if (l1.containsAll(l2)) continue outer;
                    else if (l2.containsAll(l1)) {
                        c1i.set(l2);
                        continue outer;
                    }
                }
                c.add(l2);
            }
        }
        
        static Collection findSimilarities(List o1, List o2_orig, List o2) {
            if (o1.size() == 0 || o2.size() == 0) {
                return null;
            }
            Object x1 = o1.get(0);
            List r1 = o1.subList(1, o1.size());
            Object x2 = o2.get(0);
            List r2 = o2.subList(1, o2.size());
            Object x = intersect(x1, x2);
            Collection c = null;
            if (x != null) {
                c = findSimilarities(r1, o2_orig, r2);
                if (c == null) {
                    c = new LinkedList();
                    Collection c2 = new LinkedList();
                    c2.add(x);
                    c.add(c2);
                } else {
                    for (Iterator i = c.iterator(); i.hasNext(); ) {
                        List l = (List) i.next();
                        l.add(0, x);
                    }
                }
            }
            if (x == null || !x1.equals(x2)) {
                Collection c2 = findSimilarities(o1, o2_orig, r2);
                if (c == null) c = c2;
                else if (c2 != null) addAllNew(c, c2);
                Collection c3 = findSimilarities(r1, o2_orig, o2);
                if (c == null) c = c3;
                else if (c3 != null) addAllNew(c, c3);
            }
            return c;
        }
        
        public Collection/*<Order>*/ findSimilarities(Order that) {
            if (true)
            {
                Collection f1 = this.getFlattened();
                Collection f2 = that.getFlattened();
                Assert._assert(f1.containsAll(f2));
                Assert._assert(f2.containsAll(f1));
            }
            
            Collection result = new LinkedList();
            Collection c = findSimilarities(this.list, that.list, that.list);
            for (Iterator i = c.iterator(); i.hasNext(); ) {
                List l = (List) i.next();
                if (l.size() == 1) {
                    Object elem = l.get(0);
                    if (!(elem instanceof List)) continue;
                    List l2 = (List) elem;
                    if (l2.size() == 1) continue;
                }
                result.add(new Order(l));
            }
            return result;
        }
        
        public boolean equals(Order that) {
            return list.equals(that.list);
        }
        public boolean equals(Object obj) {
            if (!(obj instanceof Order)) return false;
            return equals((Order) obj);
        }
        
        public boolean add(Object o) {
            return list.add(o);
        }
        public void add(int index, Object element) {
            list.add(index, element);
        }
        public boolean addAll(int index, Collection c) {
            return list.addAll(index,c);
        }
        public boolean addAll(Collection c) {
            return list.addAll(c);
        }
        public void clear() {
            list.clear();
        }
        public boolean contains(Object o) {
            return list.contains(o);
        }
        public boolean containsAll(Collection c) {
            return list.containsAll(c);
        }
        public Object get(int index) {
            return list.get(index);
        }
        public int hashCode() {
            return list.hashCode();
        }
        public int indexOf(Object o) {
            return list.indexOf(o);
        }
        public boolean isEmpty() {
            return list.isEmpty();
        }
        public Iterator iterator() {
            return list.iterator();
        }
        public int lastIndexOf(Object o) {
            return list.lastIndexOf(o);
        }
        public ListIterator listIterator() {
            return list.listIterator();
        }
        public ListIterator listIterator(int index) {
            return list.listIterator(index);
        }
        public Object remove(int index) {
            return list.remove(index);
        }
        public boolean remove(Object o) {
            return list.remove(o);
        }
        public boolean removeAll(Collection c) {
            return list.removeAll(c);
        }
        public boolean retainAll(Collection c) {
            return list.retainAll(c);
        }
        public Object set(int index, Object element) {
            return list.set(index, element);
        }
        public int size() {
            return list.size();
        }
        public List subList(int fromIndex, int toIndex) {
            return list.subList(fromIndex,toIndex);
        }
        public Object[] toArray() {
            return list.toArray();
        }
        public Object[] toArray(Object[] a) {
            return list.toArray(a);
        }
        public String toString() {
            return list.toString();
        }
    }
    
    public static class OrderingInfo {
        
        public double orderGoodness(Order o) {
            return 0;
        }
        
    }
    
    public static void main(String[] args) {
        OrderIterator i = generateAllOrders(Arrays.asList(args));
        int k = 0;
        while (i.hasNext()) {
            Order o = i.nextOrder();
            System.out.println((++k)+": "+o);
            OrderIterator j = generateAllOrders(Arrays.asList(args));
            while (j.hasNext()) {
                Order p = j.nextOrder();
                System.out.print(" with "+p+" = ");
                System.out.println(o.findSimilarities(p));
            }
        }
    }
    
}
