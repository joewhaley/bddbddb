// FindBestOrder.java, created Aug 21, 2004 1:17:30 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.NoSuchElementException;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.EntryValueComparator;
import org.sf.bddbddb.util.Pair;
import org.sf.bddbddb.util.PermutationGenerator;

/**
 * FindBestOrder
 * 
 * @author John Whaley
 * @version $Id$
 */
public class FindBestOrder {
    
    Map/*<InferenceRule,OrderingInfo>*/ orderInfo_rules;
    Map/*<Relation,OrderingInfo>*/ orderInfo_relations;
    
    /**
     * 
     */
    public FindBestOrder() {
        super();
        orderInfo_rules = new HashMap();
        orderInfo_relations = new HashMap();
    }
    
    public OrderingInfo getOrderInfo(InferenceRule r) {
        OrderingInfo o = (OrderingInfo) orderInfo_rules.get(r);
        if (o == null) {
            orderInfo_rules.put(r, o = new OrderingInfo());
        }
        return o;
    }
    
    /**
     * Return an iterator that iterates through all orders of a given list,
     * including interleavings.
     * 
     * @param vars  list
     * @return  iterator of all orders
     */
    public static OrderIterator generateAllOrders(List vars) {
        return new OrderIterator(vars);
    }
    
    /**
     * Iterate through all possible orders of a given list.
     * 
     * @author jwhaley
     * @version $Id$
     */
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
    
    /**
     * Represents an order.  This is just a List with a few extra utility functions.
     * 
     * @author jwhaley
     * @version $Id$
     */
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
        
        static Object intersect(Object a, Object b) {
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
        
        public Collection/*<Pair>*/ getAllInterleaveConstraints() {
            Collection s = new LinkedList();
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                Object o1 = i.next();
                if (o1 instanceof Collection) {
                    Collection c = (Collection) o1;
                    for (Iterator x = c.iterator(); x.hasNext(); ) {
                        Object a = x.next();
                        Iterator y = c.iterator();
                        while (y.hasNext() && y.next() != a) ;
                        while (y.hasNext()) {
                            Object b = y.next();
                            s.add(new Pair(x, y));
                        }
                    }
                }
            }
            return s;
        }
        
        int numInterleaveConstraints() {
            int n = 0;
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                Object o = i.next();
                if (o instanceof Collection) {
                    int k = ((Collection) o).size();
                    n += k * (k-1) / 2;
                }
            }
            return n;
        }
        
        public Collection/*<Pair>*/ getAllPrecedenceConstraints() {
            Collection s = new LinkedList();
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                Object o1 = i.next();
                Iterator j = list.iterator();
                while (j.hasNext() && j.next() != o1) ;
                while (j.hasNext()) {
                    Object o2 = j.next();
                    Iterator x, y;
                    if (o1 instanceof Collection) {
                        x = ((Collection) o1).iterator();
                    } else {
                        x = Collections.singleton(o1).iterator();
                    }
                    if (o2 instanceof Collection) {
                        y = ((Collection) o2).iterator();
                    } else {
                        y = Collections.singleton(o2).iterator();
                    }
                    while (x.hasNext()) {
                        Object x1 = x.next();
                        while (y.hasNext()) {
                            Object y1 = y.next();
                            s.add(new Pair(x1, y1));
                        }
                    }
                }
            }
            return s;
        }
        
        /**
         * Returns the similarity between two orders as a number between 0.0 and 1.0.
         * 1.0 means that the orders are exactly the same, and 0.0 means they have no
         * similarities.
         * 
         * @param that
         * @return  similarity measure between 0.0 and 1.0
         */
        public double similarity(Order that) {
            Collection thisFlat = this.getFlattened();
            Collection thatFlat = this.getFlattened();
            if (thisFlat.size() < thatFlat.size())
                return this.similarity0(that);
            else
                return that.similarity0(this);
        }
        
        public static double PRECEDENCE_WEIGHT = 1.;
        public static double INTERLEAVE_WEIGHT = 3.;
        
        double similarity0(Order that) {
            Collection dis_preds = this.getAllPrecedenceConstraints();
            Collection dis_inters = this.getAllInterleaveConstraints();
            Collection dat_preds = this.getAllPrecedenceConstraints();
            Collection dat_inters = this.getAllInterleaveConstraints();
            
            // Calculate the maximum number of similarities.
            int nPred = dis_preds.size();
            int nInter = dis_inters.size();
            
            // Find all similarities between these orders.
            dis_preds.removeAll(dat_preds);
            dis_inters.removeAll(dat_inters);
            int nPred2 = dis_preds.size();
            int nInter2 = dis_inters.size();

            double total = nPred * PRECEDENCE_WEIGHT + nInter * INTERLEAVE_WEIGHT;
            double unsimilar = nPred2 * PRECEDENCE_WEIGHT + nInter2 * INTERLEAVE_WEIGHT;
            return (total - unsimilar) / total;
        }
        
        public static double[] COMPLEXITY_SINGLE = 
        { 0., 1., 2., 3., 4., 5., 6., 7., 8., 9., 10., 11., 12., 13., 14., 15. } ;
        public static double[] COMPLEXITY_MULTI = 
        { 0., 2., 4., 8., 16., 32., 64., 128., 256., 512., 1024., 2048., 4096., 8192., 16384., 32768. } ;
        
        double complexity() {
            int n = Math.min(list.size(), COMPLEXITY_SINGLE.length-1);
            double total = COMPLEXITY_SINGLE[n];
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                Object o = i.next();
                if (o instanceof Collection) {
                    n = Math.min(((Collection) o).size(), COMPLEXITY_MULTI.length-1);
                    total += COMPLEXITY_MULTI[n];
                }
            }
            return total;
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
    
    /**
     * Holds ordering info that persists across multiple trials,
     * e.g. ordering info for a relation or a rule.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class OrderingInfo {
        Collection/*<Order>*/ knownGood;
        Collection/*<Order>*/ knownBad;
        Collection/*<Order>*/ goodOrderCharacteristics;
        Collection/*<Order>*/ badOrderCharacteristics;
        
        Collection/*<OrderingInfoUpdater>*/ children;
        
        OrderingInfo() {
            knownGood = new LinkedList();
            knownBad = new LinkedList();
            goodOrderCharacteristics = new LinkedList();
            badOrderCharacteristics = new LinkedList();
            children = new LinkedList();
        }
        
        public void registerAsGood(Order o) {
            knownGood.add(o);
        }
        
        public void registerAsBad(Order o) {
            knownBad.add(o);
        }
        
        /**
         * Given a collection of orders, find its similarities and the
         * number of occurrences of each similarity.
         * 
         * @param c  collection of orders
         * @return  map from order similarities to frequencies
         */
        static Map/*<Order,Integer>*/ calcSimilarities(Collection c) {
            Map m = new HashMap();
            for (Iterator i = c.iterator(); i.hasNext(); ) {
                Order a = (Order) i.next();
                Iterator j = c.iterator();
                while (j.hasNext() && j.next() != a) ;
                while (j.hasNext()) {
                    Order b = (Order) j.next();
                    Collection/*<Order>*/ sim = a.findSimilarities(b);
                    // todo: expand sim to also include implied suborders.
                    for (Iterator k = sim.iterator(); k.hasNext(); ) {
                        Order s = (Order) k.next();
                        Integer count = (Integer) m.get(s);
                        int newCount = (count==null) ? 1 : count.intValue()+1;
                        m.put(s, new Integer(newCount));
                    }
                }
            }
            return m;
        }
        
        /**
         * Look at the data we have collected so far to determine an order that 
         * looks to be good.
         * 
         * @return  an order that seems good, or null if there aren't any.
         */
        public Order gimmeAGoodOrder(List/*<Variable>*/ variables) {
            // Find an order that has some of the good order characteristics
            // without any of the bad ones.
            OrderIterator i = generateAllOrders(variables);
            Order bestOrder = null; double bestScore = Double.MAX_VALUE;
            while (i.hasNext()) {
                Order o = i.nextOrder();
                double score = orderGoodness(o);
                if (score > bestScore) {
                    bestScore = score;
                    bestOrder = o;
                }
            }
            return bestOrder;
        }
        
        public static double BAD_FACTOR = -5.;
        public static double GOOD_FACTOR = 1.;
        
        /**
         * Return a measure of the probable "goodness" of the given order.
         * The number is between 0.0 and 1.0, with higher numbers being better.
         * 
         * @param o  order
         * @return  probable goodness
         */
        public double orderGoodness(Order o) {
            double score = 0.;
            double min = 0., max = 0.;
            for (Iterator i = goodOrderCharacteristics.iterator(); i.hasNext(); ) {
                Order goodOrder = (Order) i.next();
                double howSimilar = o.similarity(goodOrder);
                score += howSimilar * GOOD_FACTOR;
                max += GOOD_FACTOR;
            }
            for (Iterator i = badOrderCharacteristics.iterator(); i.hasNext(); ) {
                Order badOrder = (Order) i.next();
                double howSimilar = o.similarity(badOrder);
                score += howSimilar * BAD_FACTOR;
                min += BAD_FACTOR;
            }
            return (score - min) / (max - min);
        }
        
    }
    
    /**
     * Ordering info that can be updated based on new trials.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class UpdateableOrderingInfo extends OrderingInfo {
        
        Collection/*<OrderingInfo>*/ parents;
        Map/*<Order,Long>*/ rawData;
        boolean needsUpdate;
        
        static long MIN_COST = 0L;
        static long MAX_COST = 100000000L;
        
        UpdateableOrderingInfo() {
            rawData = new HashMap();
            needsUpdate = false;
        }
        
        public void registerNewRawData(Order o, long cost) {
            rawData.put(o, new Long(cost));
            needsUpdate = true;
        }
        
        public void registerAsGood(Order o) {
            super.registerAsGood(o);
            rawData.put(o, new Long(MIN_COST));
            needsUpdate = true;
        }
        
        public void registerAsBad(Order o) {
            super.registerAsBad(o);
            rawData.put(o, new Long(MAX_COST));
            needsUpdate = true;
        }
        
        /**
         * Look at the data we have collected so far to determine an order that 
         * looks to be good.
         * 
         * @return  an order that seems good, or null if there aren't any.
         */
        public Order tryNewGoodOrder(List/*<Variables>*/ variables) {
            calculateCharacteristics();
            // Find an order that has some of the good order characteristics
            // without any of the bad ones.
            OrderIterator i = generateAllOrders(variables);
            Order bestOrder = null; double bestScore = Double.MAX_VALUE;
            while (i.hasNext()) {
                Order o = i.nextOrder();
                if (rawData.containsKey(o)) continue;
                double score = orderGoodness(o);
                if (score > bestScore) {
                    bestScore = score;
                    bestOrder = o;
                }
            }
            return bestOrder;
        }
        
        void calculateCharacteristics() {
            if (!needsUpdate) return;
            
            // Sort raw data by cost.
            Map.Entry[] sorted = (Map.Entry[]) rawData.entrySet().toArray(new Map.Entry[rawData.size()]);
            Arrays.sort(sorted, EntryValueComparator.INSTANCE);
            
            // Separate raw data into "good" and "bad".
            // For now, use the median to differentiate between good/bad.
            // In the future, we may want to use a better metric.
            int medianIndex = (sorted.length + knownGood.size() + knownBad.size()) / 2;
            medianIndex -= knownGood.size();
            Collection good = new HashSet(knownGood);
            Collection bad = new HashSet(knownBad);
            for (int i = 0; i < sorted.length; ++i) {
                Object o = sorted[i].getKey();
                if (i < medianIndex) {
                    System.out.println("Order good: "+sorted[i]);
                    good.add(o);
                } else {
                    System.out.println("Order bad: "+sorted[i]);
                    bad.add(o);
                }
            }
            
            // Find outstanding characteristics of the "good" and "bad" sets.
            Map/*<Order,Integer>*/ goodSim = calcSimilarities(good);
            Map.Entry[] sortedGoodSim = (Map.Entry[]) goodSim.entrySet().toArray(new Map.Entry[goodSim.size()]);
            Arrays.sort(sortedGoodSim, EntryValueComparator.INSTANCE);
            
            Map/*<Order,Integer>*/ badSim = calcSimilarities(bad);
            Map.Entry[] sortedBadSim = (Map.Entry[]) badSim.entrySet().toArray(new Map.Entry[badSim.size()]);
            Arrays.sort(sortedBadSim, EntryValueComparator.INSTANCE);
            
            goodOrderCharacteristics.clear();
            badOrderCharacteristics.clear();
            // Calculate the dominant (important) characteristics in each of the sets.
            // For now, use the median to differentiate between important/unimportant.
            // In the future, we may want to use a better metric.
            int goodMedianIndex = (sortedGoodSim.length) / 2;
            for (int i = sortedGoodSim.length-1; i > goodMedianIndex; --i) {
                System.out.println("Good: "+sortedGoodSim[i]);
                goodOrderCharacteristics.add(sortedGoodSim[i].getKey());
            }
            int badMedianIndex = (sortedBadSim.length) / 2;
            for (int i = sortedBadSim.length-1; i > badMedianIndex; --i) {
                System.out.println("Bad: "+sortedBadSim[i]);
                badOrderCharacteristics.add(sortedBadSim[i].getKey());
            }
            needsUpdate = false;
        }
        
        public double orderGoodness(Order o) {
            if (false) {
                double sum = 0., total = 0.;
                for (Iterator i = rawData.entrySet().iterator(); i.hasNext(); ) {
                    Map.Entry e = (Map.Entry) i.next();
                    Order o2 = (Order) e.getKey();
                    double cost = ((Long) e.getValue()).doubleValue();
                    double howSimilar = o.similarity(o2);
                    sum += cost * howSimilar;
                    total += cost;
                }
            }
            double good = super.orderGoodness(o);
            return good;
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
