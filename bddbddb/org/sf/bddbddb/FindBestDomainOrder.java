// FindBestDomainOrder.java, created Aug 21, 2004 1:17:30 AM by joewhaley
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
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.io.PrintStream;
import java.math.BigInteger;
import java.text.NumberFormat;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.CombinationGenerator;
import org.sf.bddbddb.util.EntryValueComparator;
import org.sf.bddbddb.util.Pair;

/**
 * FindBestDomainOrder
 * 
 * @author John Whaley
 * @version $Id$
 */
public class FindBestDomainOrder {
    
    public static int TRACE = 2;
    public static PrintStream out = System.out;
    
    Map/*<InferenceRule,OrderInfoCollection>*/ orderInfo_rules;
    Map/*<Relation,OrderInfoCollection>*/ orderInfo_relations;
    
    /**
     * 
     */
    public FindBestDomainOrder() {
        super();
        orderInfo_rules = new HashMap();
        orderInfo_relations = new HashMap();
    }
    
    /**
     * Get the order info collection for the given rule.
     * 
     * @param r  rule
     * @return  order info collection
     */
    public OrderInfoCollection getOrderInfo(InferenceRule r) {
        OrderInfoCollection o = (OrderInfoCollection) orderInfo_rules.get(r);
        if (o == null) {
            if (TRACE > 0) out.println("Initializing new ordering info for "+r);
            orderInfo_rules.put(r, o = new OrderInfoCollection("rule"+r.id));
        }
        return o;
    }
    
    /**
     * Get the order info collection for the given relation.
     * 
     * @param r  relation
     * @return  order info collection
     */
    public OrderInfoCollection getOrderInfo(Relation r) {
        OrderInfoCollection o = (OrderInfoCollection) orderInfo_relations.get(r);
        if (o == null) {
            if (TRACE > 0) out.println("Initializing new ordering info for "+r);
            orderInfo_relations.put(r, o = new OrderInfoCollection(r.name));
        }
        return o;
    }
    
    /**
     * Dump the collected order info for rules and relations to standard output.
     */
    public void dump() {
        for (Iterator i = orderInfo_rules.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry) i.next();
            InferenceRule ir = (InferenceRule)e.getKey();
            OrderInfoCollection info = (OrderInfoCollection)e.getValue();
            System.out.println("Rule: "+ir);
            info.dump();
        }
        for (Iterator i = orderInfo_relations.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry) i.next();
            Relation r = (Relation)e.getKey();
            OrderInfoCollection info = (OrderInfoCollection)e.getValue();
            System.out.println("Relation: "+r);
            info.dump();
        }
    }
    
    /**
     * Generate all orders of a given list of variables.
     * 
     * @param vars  list of variables
     * @return  list of all orders of those variables
     */
    public static List/*<Order>*/ generateAllOrders(List vars) {
        if (vars.size() == 0) return null;
        LinkedList result = new LinkedList();
        if (vars.size() == 1) {
            result.add(new Order(vars));
            return result;
        }
        Object car = vars.get(0);
        List recurse = generateAllOrders(vars.subList(1, vars.size()));
        for (Iterator i = recurse.iterator(); i.hasNext(); ) {
            Order order = (Order) i.next();
            for (int j = 0; j <= order.size(); ++j) {
                Order myOrder = new Order(order);
                myOrder.add(j, car);
                result.add(myOrder);
            }
        }
        for (Iterator i = recurse.iterator(); i.hasNext(); ) {
            Order order = (Order) i.next();
            for (int j = 0; j < order.size(); ++j) {
                Order myOrder = new Order(order);
                Object o = myOrder.get(j);
                List c = new LinkedList();
                c.add(car);
                if (o instanceof Collection) {
                    c.addAll((Collection)o);
                } else {
                    c.add(o);
                }
                myOrder.set(j, c);
                result.add(myOrder);
            }
        }
        return result;
    }
    
    /**
     * Return an iterator that iterates through all orders of a given list,
     * including interleavings.
     * 
     * @param vars  list
     * @return  iterator of all orders
     */
    public static OrderIterator getOrderIterator(List vars) {
        return new OrderIterator(vars);
    }
    
    /**
     * Translate from one order to another.  Used when orders have different names.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public interface OrderTranslator {
        /**
         * Translate the given order.  Always generates a new Order object, even if
         * the order does not change.
         * 
         * @param o  order
         * @return  translated order
         */
        Order translate(Order o);
    }
    
    /**
     * The identity translation.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class IdentityTranslator implements OrderTranslator {
        /**
         * Singleton instance.
         */
        public static final IdentityTranslator INSTANCE = new IdentityTranslator();
        /* (non-Javadoc)
         * @see org.sf.bddbddb.FindBestDomainOrder.OrderTranslator#translate(org.sf.bddbddb.FindBestDomainOrder.Order)
         */
        public Order translate(Order o) { return new Order(new LinkedList(o)); }
    }
    
    /**
     * Translator based on a map.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class MapBasedTranslator implements OrderTranslator {
        
        Map m;
        
        public MapBasedTranslator(Map m) {
            this.m = m;
        }
        
        /**
         * direction == true means map from rule to relation.
         * direction == false means map from relation to rule.
         * 
         * @param ir  rule
         * @param r  relation
         * @param direction  true=rule->relation, false=relation->rule
         */
        public MapBasedTranslator(InferenceRule ir, Relation r, boolean direction) {
            m = new HashMap();
            for (Iterator i = ir.top.iterator(); i.hasNext(); ) {
                RuleTerm rt = (RuleTerm) i.next();
                if (rt.relation != r) continue;
                Assert._assert(r.attributes.size() == rt.variables.size());
                for (int j = 0; j < r.attributes.size(); ++j) {
                    Attribute a = (Attribute) r.attributes.get(j);
                    Variable v = (Variable) rt.variables.get(j);
                    // Note: this doesn't match exactly if a relation appears
                    // twice in a rule.
                    if (direction)
                        m.put(v, a);
                    else
                        m.put(a, v);
                }
            }
        }
        
        /**
         * direction == true means map from ruleterm to relation.
         * direction == false means map from relation to ruleterm.
         * 
         * @param rt  ruleterm
         * @param direction  true=ruleterm->relation, false=relation->ruleterm
         */
        public MapBasedTranslator(RuleTerm rt, boolean direction) {
            m = new HashMap();
            Relation r = rt.relation;
            Assert._assert(r.attributes.size() == rt.variables.size());
            for (int j = 0; j < r.attributes.size(); ++j) {
                Attribute a = (Attribute) r.attributes.get(j);
                Variable v = (Variable) rt.variables.get(j);
                if (direction)
                    m.put(v, a);
                else
                    m.put(a, v);
            }
        }
        
        /* (non-Javadoc)
         * @see org.sf.bddbddb.FindBestDomainOrder.OrderTranslator#translate(org.sf.bddbddb.FindBestDomainOrder.Order)
         */
        public Order translate(Order o) {
            if (TRACE > 2) System.out.print("Translating "+o);
            LinkedList result = new LinkedList();
            for (Iterator i = o.iterator(); i.hasNext(); ) {
                Object a = i.next();
                if (a instanceof Collection) {
                    Collection result2 = new LinkedList();
                    for (Iterator j = ((Collection) a).iterator(); j.hasNext(); ) {
                        Object a2 = j.next();
                        Object b2 = m.get(a2);
                        if (b2 != null) result2.add(b2);
                    }
                    if (result2.size() > 1) {
                        result.add(result2);
                    } else if (!result2.isEmpty()) {
                        result.add(result2.iterator().next());
                    }
                } else {
                    Object b = m.get(a);
                    if (b != null) result.add(b);
                }
            }
            if (TRACE > 2) System.out.println(" -> "+result);
            return new Order(result);
        }
    }
    
    /**
     * Iterate through all possible orders of a given list.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class OrderIterator implements Iterator {
        
        List orig;
        List/*<CombinationGenerator>*/ combos;
        int comboCounter;
        
        public OrderIterator(List a) {
            orig = new ArrayList(a);
            combos = new ArrayList(a.size());
            comboCounter = 0;
            gotoNextCombo();
        }
        
        void gotoNextCombo() {
            combos.clear();
            int remaining = orig.size();
            int size = 1;
            int bits = comboCounter++;
            while (remaining > 0) {
                CombinationGenerator g;
                if (remaining == size) {
                    g = new CombinationGenerator(remaining, size);
                    if (!combos.isEmpty()) g.getNext();
                    combos.add(g);
                    break;
                }
                if ((bits&1)==0) {
                    g = new CombinationGenerator(remaining, size);
                    if (!combos.isEmpty()) g.getNext();
                    combos.add(g);
                    remaining -= size;
                    size = 0;
                }
                size++;
                bits >>= 1;
            }
        }
        
        boolean hasNextCombo() {
            int elements = orig.size();
            return (comboCounter < (1 << (elements-1)));
        }
        
        boolean hasMore() {
            for (Iterator i = combos.iterator(); i.hasNext(); ) {
                CombinationGenerator g = (CombinationGenerator) i.next();
                if (g.hasMore()) return true;
            }
            return false;
        }
        
        public boolean hasNext() {
            return hasMore() || hasNextCombo();
        }
        
        public Object next() {
            return nextOrder();
        }
        
        public Order nextOrder() {
            if (!hasMore()) {
                if (!hasNextCombo()) {
                    throw new NoSuchElementException();
                }
                gotoNextCombo();
            }
            List result = new LinkedList();
            List used = new ArrayList(orig);
            boolean carry = true;
            for (Iterator i = combos.iterator(); i.hasNext(); ) {
                CombinationGenerator g = (CombinationGenerator) i.next();
                int[] p;
                if (carry) {
                    if (!g.hasMore()) g.reset();
                    else carry = false;
                    p = g.getNext();
                } else {
                    p = g.getCurrent();
                }
                if (p.length == 1) {
                    result.add(used.remove(p[0]));
                } else {
                    LinkedList c = new LinkedList();
                    for (int k = p.length-1; k >= 0; --k) {
                        c.addFirst(used.remove(p[k]));
                    }
                    result.add(c);
                }
            }
            Assert._assert(!carry);
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
    public static class Order implements List, Comparable {
        List list;
        
        public Order(Order o) {
            this.list = new LinkedList(o.list);
        }
        
        public Order(List l) {
            this.list = l;
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
            if (TRACE > 1) out.println("Calculating similarities in the collection: "+c);
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
            if (TRACE > 1) out.println("Similarities: "+m);
            return m;
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
        
        // TODO: this should use a dynamic programming implementation instead
        // of recursive, because it is solving many repeated subproblems.
        static Collection findSimilarities(List o1, List o2) {
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
                c = findSimilarities(r1, r2);
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
                Collection c2 = findSimilarities(o1, r2);
                if (c == null) c = c2;
                else if (c2 != null) addAllNew(c, c2);
                Collection c3 = findSimilarities(r1, o2);
                if (c == null) c = c3;
                else if (c3 != null) addAllNew(c, c3);
            }
            return c;
        }
        
        public Collection/*<Order>*/ findSimilarities(Order that) {
            if (false)
            {
                Collection f1 = this.getFlattened();
                Collection f2 = that.getFlattened();
                Assert._assert(f1.containsAll(f2));
                Assert._assert(f2.containsAll(f1));
            }
            
            Collection result = new LinkedList();
            Collection c = findSimilarities(this.list, that.list);
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
         * Precedence constraints are weighted by the factor "PRECEDENCE_WEIGHT", and
         * interleave constraints are weighted by the factor "INTERLEAVE_WEIGHT".
         * 
         * @param that
         * @return  similarity measure between 0.0 and 1.0
         */
        public double similarity(Order that) {
            if (this.isEmpty() || that.isEmpty()) return 1.;
            Collection thisFlat = this.getFlattened();
            Collection thatFlat = this.getFlattened();
            if (thisFlat.size() < thatFlat.size())
                return this.similarity0(that);
            else
                return that.similarity0(this);
        }
        
        public static double PRECEDENCE_WEIGHT = 1.;
        public static double INTERLEAVE_WEIGHT = 3.;
        
        private double similarity0(Order that) {
            Collection dis_preds = this.getAllPrecedenceConstraints();
            Collection dis_inters = this.getAllInterleaveConstraints();
            Collection dat_preds = that.getAllPrecedenceConstraints();
            Collection dat_inters = that.getAllInterleaveConstraints();
            
            // Calculate the maximum number of similarities.
            int nPred = dis_preds.size();
            int nInter = dis_inters.size();
            
            // Find all similarities between the orders.
            dis_preds.removeAll(dat_preds);
            dis_inters.removeAll(dat_inters);
            int nPred2 = dis_preds.size();
            int nInter2 = dis_inters.size();

            double total = nPred * PRECEDENCE_WEIGHT + nInter * INTERLEAVE_WEIGHT;
            double unsimilar = nPred2 * PRECEDENCE_WEIGHT + nInter2 * INTERLEAVE_WEIGHT;
            double sim = (total - unsimilar) / total;
            if (TRACE > 4) out.println("Similarity ("+this+" and "+that+") = "+format(sim));
            return sim;
        }
        
        public static double[] COMPLEXITY_SINGLE = 
        { 0., 1., 2., 3., 4., 5., 6., 7., 8., 9., 10., 11., 12., 13., 14., 15. } ;
        public static double[] COMPLEXITY_MULTI = 
        { 0., 2., 4., 8., 16., 32., 64., 128., 256., 512., 1024., 2048., 4096., 8192., 16384., 32768. } ;
        
        /**
         * Returns a measure of the complexity of this order.  Higher numbers are
         * more complex (i.e. have more constraints)
         * 
         * @return a measure of the complexity of this order
         */
        public double complexity() {
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
        
        /**
         * @param arg0
         * @return
         */
        public int compareTo(Object arg0) {
            return compareTo((Order) arg0);
        }
        /**
         * Compares orders lexigraphically. 
         * 
         * @param that  order to compare to
         * @return  -1, 0, or 1 if this order is less than, equal to, or greater than
         */
        public int compareTo(Order that) {
            return this.toString().compareTo(that.toString());
        }
        
        public boolean equals(Order that) {
            return list.equals(that.list);
        }
        /* (non-Javadoc)
         * @see java.lang.Object#equals(java.lang.Object)
         */
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
    
    static NumberFormat nf;
    /**
     * Format a double as a percentage.
     * 
     * @param d  double
     * @return  string representation
     */
    public static String format(double d) {
        if (nf == null) {
            nf = NumberFormat.getPercentInstance();
            nf.setMaximumFractionDigits(2);
        }
        return nf.format(d);
    }
    
    /**
     * Calculated information about an order.  This consists of a score
     * and a confidence.
     * 
     * @author John Whaley
     * @version $Id$
     */
    public static class OrderInfo implements Comparable {
        
        /**
         * The order this information is about.
         */
        Order order;
        
        /**
         * A measure of how good this order is.  Ranges from 0.0 to 1.0.
         * 0.0 is the worst possible, and 1.0 is the best.
         */
        double score;
        
        /**
         * A measure of the confidence of this score.  Higher is better.
         * This is also a measure of how much time was spent on the measured operations.
         * Longer operations have higher confidence ratings.  Therefore,
         * the confidence can also be used as the importance.
         */
        double confidence;
        
        /**
         * Construct a new OrderInfo.
         * 
         * @param o  order
         * @param s  score
         * @param c  confidence
         */
        public OrderInfo(Order o, double s, double c) {
            this.order = o;
            this.score = s;
            this.confidence = c;
        }
        
        /**
         * Construct a new OrderInfo that is a clone of another.
         * 
         * @param that  other OrderInfo to clone from
         */
        public OrderInfo(OrderInfo that) {
            this.order = that.order;
            this.score = that.score;
            this.confidence = that.confidence;
        }
        
        /**
         * Update the score and confidence to take into account another order info.
         * Assumes that the two are referring to the same order.
         * 
         * @param that  order to incorporate
         */
        public void update(OrderInfo that) {
            update(that.order, that.score, that.confidence);
        }
        public void update(Order that_order, double that_score, double that_confidence) {
            if (this.confidence + that_confidence < 0.0001) {
                // Do not update the score if the confidence is too low.
                return;
            }
            double newScore = (this.score * this.confidence + that_score * that_confidence) /
                              (this.confidence + that_confidence);
            // todo: this confidence calculation seems slightly bogus, but seems
            // to give reasonable answers.
            double diff = (this.score - newScore);
            double diffSquared = diff * diff;
            double newConfidence = (this.confidence + that_confidence) / (diffSquared + 1.);
            if (TRACE > 4) out.println("Updating info: "+this+" * score "+format(that_score)+" confidence "+format(that_confidence)+
                                       " -> score "+format(newScore)+" confidence "+format(newConfidence));
            this.score = newScore;
            this.confidence = newConfidence;
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return order+": score "+format(score)+" confidence "+format(confidence);
        }

        /* (non-Javadoc)
         * @see java.lang.Comparable#compareTo(java.lang.Object)
         */
        public int compareTo(Object arg0) {
            return compareTo((OrderInfo) arg0);
        }
        /**
         * Comparison operator for OrderInfo objects.  Score is most important, followed
         * by confidence.  If both are equal, we compare the order lexigraphically.
         * 
         * @param that  OrderInfo to compare to
         * @return  -1, 0, or 1 if this OrderInfo is less than, equal to, or greater than the other
         */
        public int compareTo(OrderInfo that) {
            int result = (int) Math.signum(this.score - that.score);
            if (result == 0) {
                result = (int) Math.signum(this.confidence - that.confidence);
                if (result == 0) {
                    result = this.order.compareTo(that.order);
                }
            }
            return result;
        }
    }
    
    /**
     * Information about a particular trial.
     * 
     * @author John Whaley
     * @version $Id$
     */
    public static class TrialInfo implements Comparable {
        /**
         * Order tried.
         */
        Order order;
        /**
         * Cost of this trial.
         */
        long cost;
        
        /**
         * Construct a new TrialInfo.
         * 
         * @param o  order
         * @param c  cost
         */
        public TrialInfo(Order o, long c) {
            this.order = o;
            this.cost = c;
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return order+": cost "+cost;
        }

        /* (non-Javadoc)
         * @see java.lang.Comparable#compareTo(java.lang.Object)
         */
        public int compareTo(Object arg0) {
            return compareTo((TrialInfo) arg0);
        }
        
        /**
         * Comparison operator for TrialInfo objects.  Comparison is based on cost.
         * If the cost is equal, we compare the order lexigraphically.
         * 
         * @param that  TrialInfo to compare to
         * @return  -1, 0, or 1 if this TrialInfo is less than, equal to, or greater than the other
         */
        public int compareTo(TrialInfo that) {
            int result = Long.signum(this.cost - that.cost);
            if (result == 0) {
                result = this.order.compareTo(that.order);
            }
            return result;
        }
    }
    
    /**
     * A collection of trials on the same test.  (The same BDD operation.)
     * 
     * @author John Whaley
     * @version $Id$
     */
    public static class TrialCollection {
        /**
         * Name of the test.
         */
        String name;
        
        /**
         * Map from orders to their trial information.
         */
        Map/*<Order,TrialInfo>*/ trials;
        
        /**
         * Trial info sorted by cost.  Updated automatically when necessary.
         */
        transient TrialInfo[] sorted;
        
        /**
         * Construct a new collection of trials with the given test name.
         * 
         * @param n  test name
         */
        public TrialCollection(String n) {
            name = n;
            trials = new LinkedHashMap();
            sorted = null;
        }
        
        /**
         * Add the information about a trial to this collection.
         * 
         * @param i  trial info
         */
        public void addTrial(TrialInfo i) {
            if (TRACE > 1) out.println(this+": Adding trial "+i);
            trials.put(i.order, i);
            sorted = null;
        }
        
        /**
         * Add the information about a trial to this collection.
         * 
         * @param o  order
         * @param cost  cost of operation
         */
        public void addTrial(Order o, long cost) {
            addTrial(new TrialInfo(o, cost));
        }
        
        /**
         * Returns true if this collection contains a trial with the given order,
         * false otherwise.
         * 
         * @param o  order
         * @return  true if this collection contains it, false otherwise
         */
        public boolean contains(Order o) {
            return trials.containsKey(o);
        }
        
        /**
         * Given an order, make a prediction based on the other trials about
         * the cost of the order on the tested operation.  We should not have
         * already tested this order.  The result contains both a score and
         * a confidence rating.
         * 
         * This works by computing the similarities between the given order and
         * the tested orders and weighing each score based on the amount of
         * similarity.  It may not be entirely accurate as it weighs all
         * similarities equally, but it is a rough approximation.
         * 
         * @param o  order to predict
         * @return  predicted score and confidence rating of that prediction
         */
        public OrderInfo predict(Order o) {
            Assert._assert(!trials.containsKey(o));
            if (TRACE > 2) out.println(this+": Predicting "+o);
            OrderInfo result = new OrderInfo(o, 0.5, 0.);
            if (size() >= 2) {
                TrialInfo[] sorted = getSorted();
                long min = sorted[0].cost;
                long max = sorted[sorted.length-1].cost;
                double range = (double)max - (double)min;
                for (int i = 0; i < sorted.length; ++i) {
                    if (TRACE > 3) out.println(this+": comparing to "+sorted[i]);
                    double score = (range < 0.0001) ? 0.5 : ((double)(max - sorted[i].cost) / range);
                    double sim = o.similarity(sorted[i].order);
                    result.update(o, score, (range < 0.0001) ? 0. : sim);
                }
            }
            if (TRACE > 2) out.println(this+": final prediction = "+result);
            return result;
        }
        
        /**
         * @return  the standard deviation of the trials
         */
        public double getStdDev() {
            return Math.sqrt(getVariance());
        }
        
        /**
         * @return  the variance of the trials
         */
        public double getVariance() {
            double sum = 0.;
            double sumOfSquares = 0.;
            int n = 0;
            for (Iterator i = trials.values().iterator(); i.hasNext(); ++n) {
                TrialInfo t = (TrialInfo) i.next();
                double c = (double) t.cost;
                sum += c;
                sumOfSquares += c * c;
            }
            // variance = (n*sum(X^2) - (sum(X)^2))/n^2
            double variance = (sumOfSquares * n - sum * sum) / (n * n);
            return variance;
        }
        
        /**
         * @return  the minimum cost trial
         */
        public TrialInfo getMinimum() {
            TrialInfo best = null;
            for (Iterator i = trials.values().iterator(); i.hasNext(); ) {
                TrialInfo t = (TrialInfo) i.next();
                if (best == null || t.cost < best.cost)
                    best = t;
            }
            return best;
        }
        
        /**
         * @return  the maximum cost trial
         */
        public TrialInfo getMaximum() {
            TrialInfo best = null;
            for (Iterator i = trials.values().iterator(); i.hasNext(); ) {
                TrialInfo t = (TrialInfo) i.next();
                if (best == null || t.cost > best.cost)
                    best = t;
            }
            return best;
        }
        
        /**
         * @return  the mean of the trials
         */
        public long getAverage() {
            long total = 0;
            int count = 0;
            for (Iterator i = trials.values().iterator(); i.hasNext(); ++count) {
                TrialInfo t = (TrialInfo) i.next();
                total += t.cost;
            }
            if (count == 0) return 0L;
            else return total / count;
        }
        
        /**
         * @return  the trials sorted by increasing cost
         */
        public TrialInfo[] getSorted() {
            if (sorted == null) {
                sorted = (TrialInfo[]) trials.values().toArray(new TrialInfo[trials.size()]);
                Arrays.sort(sorted);
            }
            return sorted;
        }
        
        /**
         * @return the number of trials in this collection
         */
        public int size() {
             return trials.size();
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return name+"@"+Integer.toHexString(this.hashCode());
        }
    }
    
    /**
     * Holds ordering info that persists across multiple trials,
     * e.g. ordering info for a relation or a rule.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class OrderInfoCollection {
        
        /**
         * Name of this order info collection (i.e. name of the relation or rule)
         */
        String name;
        
        /**
         * Map from orders to their info.
         */
        Map/*<Order,OrderInfo>*/ infos;
        
        /**
         * Order info sorted by cost.  Updated automatically when necessary.
         */
        transient OrderInfo[] sorted;
        
        /**
         * Construct a new OrderInfoCollection with the given name
         * 
         * @param s  name
         */
        public OrderInfoCollection(String s) {
            name = s;
            infos = new LinkedHashMap();
            sorted = null;
        }
        
        /**
         * Construct a new OrderInfoCollection that is the clone of another one.
         * 
         * @param that  OrderInfoCollection to clone
         */
        public OrderInfoCollection(OrderInfoCollection that) {
            this.name = that.name;
            this.infos = new LinkedHashMap(that.infos);
            this.sorted = null;
        }
        
        /**
         * Incorporate the given collection into this one, scaling all of the confidences
         * in the given collection by the given number.
         * 
         * @param that  collection to incorporate
         * @param confidence  confidence level to scale the info in the given collection by
         */
        public void incorporateInfoCollection(OrderInfoCollection that, double confidence) {
            incorporateInfoCollection(that, IdentityTranslator.INSTANCE, confidence);
        }
        /**
         * Incorporate the given collection into this one, translating orders using
         * the given translator and scaling all of the confidences by the given number.
         * 
         * @param that  collection to incorporate
         * @param t  order translator
         * @param confidence  confidence level to scale the info in the given collection by
         */
        public void incorporateInfoCollection(OrderInfoCollection that, OrderTranslator t, double confidence) {
            if (TRACE > 0) out.println(this+": incorporating info collection "+that+" with confidence "+format(confidence));
            for (Iterator i = that.infos.values().iterator(); i.hasNext(); ) {
                OrderInfo info = (OrderInfo) i.next();
                Order o = t.translate(info.order);
                double s = info.score;
                double c = info.confidence * confidence;
                incorporateInfo(o, s, c);
            }
        }
        
        /**
         * Incorporate trials into this info collection using the given confidence
         * rating for the trials.
         * 
         * @param c  trial collection to incorporate
         * @param confidence  confidence rating for trials
         */
        public void incorporateTrials(TrialCollection c, double confidence) {
            incorporateTrials(c, IdentityTranslator.INSTANCE, confidence);
        }
        
        /**
         * Incorporate trials into this info collection using the given confidence
         * rating for the trials, translating orders with the given translator. 
         * 
         * @param c  trial collection to incorporate
         * @param t  order translator
         * @param confidence  confidence rating for trials
         */
        public void incorporateTrials(TrialCollection c, OrderTranslator t, double confidence) {
            if (c.size() > 0) {
                if (TRACE > 0) out.println(this+": incorporating trials "+c+" with confidence "+format(confidence));
                TrialInfo[] ti = c.getSorted();
                long min = ti[0].cost;
                long max = ti[ti.length-1].cost;
                double range = (double)max - (double)min;
                Set visitedOrders = new HashSet();
                for (int i = 0; i < ti.length; ++i) {
                    Order o = t.translate(ti[i].order);
                    boolean isNew = visitedOrders.add(o);
                    if (TRACE > 1) out.println(this+": trial "+ti[i]+" isNew: "+isNew);
                    double score = (range < 0.0001) ? 0.5 : ((double)(max - ti[i].cost) / range);
                    double myConf = (range < 0.0001) ? 0. : confidence;
                    if (isNew && ti[i].cost >= UpdatableOrderInfoCollection.MAX_COST) {
                        myConf *= HIGH_CONFIDENCE;
                    }
                    incorporateInfo(o, score, myConf);
                }
            }
        }
        
        /**
         * Incorporate a single data point of order info.
         * 
         * @param o  order
         * @param s  score
         * @param c  confidence
         */
        public void incorporateInfo(Order o, double s, double c) {
            OrderInfo info = (OrderInfo) infos.get(o);
            if (info == null) {
                infos.put(o, info = new OrderInfo(o, s, c));
                if (TRACE > 1) out.println(this+": incorporating new info "+info);
            } else {
                if (TRACE > 1) out.println(this+": updating info "+info+" with score="+format(s)+" confidence="+format(c));
                info.update(o, s, c);
            }
            if (false) {
                for (Iterator i = infos.values().iterator(); i.hasNext(); ) {
                    OrderInfo info2 = (OrderInfo) i.next();
                    if (info == info2) continue;
                    if (o.similarity(info2.order) >= 1.0) {
                        if (TRACE > 1) out.println(this+": updating info "+info2+" with score="+format(s)+" confidence="+format(c));
                        info2.update(o, s, c);
                    }
                }
            }
            sorted = null;
        }
        
        /**
         * Incorporate a single data point of order info.
         * 
         * @param i  order info to incorporate
         */
        public void incorporateInfo(OrderInfo i) {
            OrderInfo info = (OrderInfo) infos.get(i.order);
            if (info == null) {
                infos.put(i.order, info = i);
                if (TRACE > 1) out.println(this+": incorporating new info "+info);
            } else {
                if (TRACE > 1) out.println(this+": updating info "+info+" with score="+format(i.score)+" confidence="+format(i.confidence));
                info.update(i);
            }
            if (false) {
                for (Iterator j = infos.values().iterator(); j.hasNext(); ) {
                    OrderInfo info2 = (OrderInfo) j.next();
                    if (info == info2) continue;
                    if (i.order.similarity(info2.order) >= 1.0) {
                        if (TRACE > 1) out.println(this+": updating info "+info2+" with score="+format(i.score)+" confidence="+format(i.confidence));
                        info2.update(i);
                    }
                }
            }
            sorted = null;
        }
        
        /**
         * Get the order info for the given total order.
         * Returns null if there is no info for the given order.
         * 
         * @param o  total order
         * @return  order info, or null if there is none.
         */
        public OrderInfo getTotalOrderInfo(Order o) {
            return (OrderInfo) infos.get(o);
        }
        
        /**
         * Get order info for the given partial order.  Combines the 
         * information from all orders that match.
         * Returns null if no orders match.
         * 
         * @param p  partial order
         * @return  order info, or null if no orders match.
         */
        public OrderInfo getPartialOrderInfo(Order p) {
            OrderInfo result = null;
            for (Iterator i = infos.values().iterator(); i.hasNext(); ) {
                OrderInfo info = (OrderInfo) i.next();
                if (p.similarity(info.order) >= 1.) {
                    if (result == null) result = new OrderInfo(info);
                    else result.update(info);
                }
            }
            return result;
        }
        
        
        /**
         * Create an updatable version of this order collection.  The updatable
         * one can be updated based on trials.
         * 
         * @return  updatable version of this order
         */
        public UpdatableOrderInfoCollection createUpdatable() {
            UpdatableOrderInfoCollection i = new UpdatableOrderInfoCollection(this);
            return i;
        }
        
        static double HIGH_CONFIDENCE = 10000.;
        
        /**
         * Register the given order as good.
         * This gives it a high score with a high confidence.
         * 
         * @param o  order to register as good
         */
        public void registerAsGood(Order o) {
            if (TRACE > 0) out.println(this+": Registering as a known good order: "+o);
            infos.put(o, new OrderInfo(o, 1., HIGH_CONFIDENCE));
            sorted = null;
        }
        
        /**
         * Register the given order as bad.
         * This gives it a low score with a high confidence.
         * 
         * @param o  order to register as good
         */
        public void registerAsBad(Order o) {
            if (TRACE > 0) out.println(this+": Registering as a known bad order: "+o);
            infos.put(o, new OrderInfo(o, 0., HIGH_CONFIDENCE));
            sorted = null;
        }
        
        /**
         * Returns the number of orders that are potentially "good".  A potentially
         * "good" order is one that has not been tested, a score greater than 5%, or a
         * confidence less than 1.
         * 
         * @param variables  list of variables in the order
         * @return  number of potentially good orders
         */
        public int numberOfGoodOrders(List/*<Variable>*/ variables) {
            Iterator i = generateAllOrders(variables).iterator();
            int count = 0;
            while (i.hasNext()) {
                Order o = (Order) i.next();
                OrderInfo score = (OrderInfo) infos.get(o);
                if (score == null || score.score > 0.05 || score.confidence < 1.) {
                    ++count;
                }
            }
            return count;
        }
        
        /**
         * Look at the data we have collected so far to determine an order that 
         * looks to be good.
         * 
         * @return  an order that seems good, or null if there aren't any.
         */
        public Order gimmeAGoodOrder(List/*<Variable>*/ variables) {
            Iterator i = generateAllOrders(variables).iterator();
            // Find the order with the highest score.
            // todo: should be also consider the confidence?
            Order bestOrder = null; double bestScore = 0.;
            while (i.hasNext()) {
                Order o = (Order) i.next();
                OrderInfo score = orderGoodness(o);
                if (TRACE > 1) out.println(this+": "+score);
                if (score.score > bestScore) {
                    bestScore = score.score;
                    bestOrder = o;
                }
            }
            if (TRACE > 0) out.println(this+": best order "+bestOrder+" score "+format(bestScore));
            return bestOrder;
        }
        
        /**
         * Return a measure of the probable "goodness" of the given order, and
         * a confidence of that score.
         * The score is between 0.0 and 1.0, with higher numbers being better.
         * If we already have info about a given order, use it.
         * 
         * @param o  order
         * @return  probable goodness and confidence of that rating
         */
        public OrderInfo orderGoodness(Order o) {
            OrderInfo result = (OrderInfo) infos.get(o);
            if (result != null) return result;

            if (TRACE > 2) out.print(this+": Calculating goodness of "+o);
            double score = 0.;
            double max = 0.;
            for (Iterator i = infos.values().iterator(); i.hasNext(); ) {
                OrderInfo info = (OrderInfo) i.next();
                // todo:
                //   similarity calculation doesn't take into account how important
                //   each constraint is.
                double howSimilar = o.similarity(info.order);
                double howConfident = howSimilar * info.confidence;
                score += info.score * howConfident;
                max += howConfident;
            }
            double resultScore = (max < 0.0001) ? 0.5 : (score / max); 
            
            // todo: this confidence calculation seems bogus.
            // todo: could also make this more efficient.
            double resultConfidence = 0.;
            for (Iterator i = infos.values().iterator(); i.hasNext(); ) {
                OrderInfo info = (OrderInfo) i.next();
                double howSimilar = o.similarity(info.order);
                double howConfident = howSimilar * info.confidence;
                double diff = (info.score - resultScore);
                double diffSquared = diff * diff;
                resultConfidence = (resultConfidence + howConfident) / (diffSquared + 1.);
            }
            
            result = new OrderInfo(o, resultScore, resultConfidence);
            if (TRACE > 2) out.println(" = score "+format(resultScore)+" confidence "+format(resultConfidence));
            return result;
        }
        
        /**
         * Get the order info sorted by score.
         * 
         * @return  sorted array of OrderInfo[]
         */
        public OrderInfo[] getSorted() {
            if (sorted == null) {
                sorted = (OrderInfo[]) infos.values().toArray(new OrderInfo[infos.size()]);
                Arrays.sort(sorted);
            }
            return sorted;
        }
        
        Collection/*<OrderInfo>*/ goodCharacteristics;
        Collection/*<OrderInfo>*/ badCharacteristics;
        
        /**
         * Compute the prevaling characteristics of "good" and "bad" orders.
         */
        public void calculateCharacteristics() {
            if (infos.isEmpty()) return;
            if (TRACE > 0) out.println(this+": updating characteristics...");
            
            // Choose cutoff for "good" and "bad".
            OrderInfo[] si = getSorted();
            double lowScore = si[0].score;
            double highScore = si[si.length-1].score;
            if (lowScore > 0.5) {
                if (TRACE > 0) out.println(this+": low score is too good: "+format(lowScore));
                return;
            }
            if (highScore < 0.5) {
                if (TRACE > 0) out.println(this+": high score is too bad: "+format(highScore));
                return;
            }
            double diff = highScore - lowScore; 
            if (diff < 0.1) {
                if (TRACE > 0) out.println(this+": not enough differentiation: "+format(diff));
                return;
            }
            double lowCutoff, highCutoff;
            lowCutoff = lowScore + diff * 0.3;
            highCutoff = highScore - diff * 0.3;
            Collection good = new LinkedList();
            Collection bad = new LinkedList();
            for (int i = 0; si[i].score < lowCutoff; ++i) {
                bad.add(si[i].order);
            }
            for (int i = si.length-1; si[i].score > highCutoff; --i) {
                good.add(si[i].order);
            }
            
            // Find outstanding characteristics of the "good" and "bad" sets.
            Map/*<Order,Integer>*/ goodSim = Order.calcSimilarities(good);
            Map/*<Order,Integer>*/ badSim = Order.calcSimilarities(bad);
            
            Map.Entry[] sortedGoodSim = (Map.Entry[]) goodSim.entrySet().toArray(new Map.Entry[goodSim.size()]);
            Arrays.sort(sortedGoodSim, EntryValueComparator.INSTANCE);
            if (TRACE > 0) out.println(this+": similarities of good set: "+Arrays.toString(sortedGoodSim));
            if (TRACE > 0) out.println(this+": similarities of bad set: "+badSim);
            
            if (goodCharacteristics == null) goodCharacteristics = new LinkedList();
            else goodCharacteristics.clear();
            if (badCharacteristics == null) badCharacteristics = new LinkedList();
            else badCharacteristics.clear();
            // Calculate the dominant (important) characteristics in each of the sets.
            // For now, use the median to differentiate between important/unimportant.
            // In the future, we may want to use a better metric.
            int goodMedianIndex = (sortedGoodSim.length) / 2;
            for (int i = sortedGoodSim.length-1; i >= goodMedianIndex; --i) {
                Order o = (Order) sortedGoodSim[i].getKey();
                Integer howGood = (Integer) sortedGoodSim[i].getValue();
                Integer howBad = (Integer) badSim.get(o);
                if (howBad == null || howGood.intValue() > howBad.intValue()) {
                    if (TRACE > 0) out.println("Good: "+sortedGoodSim[i]);
                    goodCharacteristics.add(sortedGoodSim[i].getKey());
                    badSim.remove(o);
                }
            }
            
            Map.Entry[] sortedBadSim = (Map.Entry[]) badSim.entrySet().toArray(new Map.Entry[badSim.size()]);
            Arrays.sort(sortedBadSim, EntryValueComparator.INSTANCE);
            
            int badMedianIndex = (sortedBadSim.length) / 2;
            for (int i = sortedBadSim.length-1; i >= badMedianIndex; --i) {
                if (TRACE > 0) out.println("Bad: "+sortedBadSim[i]+" score: "+sortedBadSim[i].getValue());
                badCharacteristics.add(sortedBadSim[i].getKey());
            }
            if (TRACE > 0) out.println(this+": finished update.");
        }
        
        /**
         * Dump the order info to the screen.
         */
        public void dump() {
            OrderInfo[] sorted = getSorted();
            System.out.println("Best orders:");
            for (int j = sorted.length-1; j >= 0 && j >= sorted.length-10; --j) {
                System.out.println(sorted[j]);
            }
            System.out.println("Worst orders:");
            for (int j = 0; j < 10 && j < sorted.length; ++j) {
                System.out.println(sorted[j]);
            }
            calculateCharacteristics();
            System.out.println("Good order characteristics: "+goodCharacteristics);
            System.out.println("Bad order characteristics: "+badCharacteristics);
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return name + "@" + Integer.toHexString(this.hashCode());
        }
    }
    
    /**
     * Ordering info that can be updated based on new trials.
     * 
     * Note: OED says "updatable" is the correct spelling, rather than "updateable".
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class UpdatableOrderInfoCollection extends OrderInfoCollection {
        
        /**
         * Collection of trials.
         */
        TrialCollection trials;
        
        static long MIN_COST = 0L;
        static long MAX_COST = 10000000L;
        
        /**
         * Construct an UpdatableOrderInfoCollection with the given name.
         * 
         * @param s  name
         */
        UpdatableOrderInfoCollection(String s) {
            super(s);
            trials = new TrialCollection(s);
        }
        
        UpdatableOrderInfoCollection(OrderInfoCollection that) {
            super(that);
            trials = new TrialCollection(that.name);
        }
        
        /**
         * Register a new trial.
         * 
         * @param o  order tried
         * @param cost  cost of trial
         */
        public void registerNewTrial(Order o, long cost) {
            if (cost >= MAX_COST) {
                registerAsBad(o);
                return;
            }
            if (TRACE > 0) out.println(this+": registering new raw data "+o+" score "+cost);
            TrialInfo i = new TrialInfo(o, cost);
            trials.addTrial(i);
        }
        
        /* (non-Javadoc)
         * @see org.sf.bddbddb.FindBestDomainOrder.OrderInfoCollection#registerAsGood(org.sf.bddbddb.FindBestDomainOrder.Order)
         */
        public void registerAsGood(Order o) {
            super.registerAsGood(o);
            TrialInfo i = new TrialInfo(o, MIN_COST);
            trials.addTrial(i);
        }
        
        /* (non-Javadoc)
         * @see org.sf.bddbddb.FindBestDomainOrder.OrderInfoCollection#registerAsBad(org.sf.bddbddb.FindBestDomainOrder.Order)
         */
        public void registerAsBad(Order o) {
            super.registerAsBad(o);
            TrialInfo i = new TrialInfo(o, MAX_COST);
            trials.addTrial(i);
        }
        
        /**
         * Look at the data we have collected so far to determine an order that 
         * looks to be good.
         * 
         * @return  an order that seems good, or null if there aren't any.
         */
        public Order tryNewGoodOrder(List/*<Variables>*/ variables) {
            if (TRACE > 1) out.println(this+": generating new orders for "+variables);
            // Find the order with the highest score that we haven't tried yet
            // and that is still possibly good.
            // todo: should be also consider the confidence?
            Iterator i = generateAllOrders(variables).iterator();
            Order bestOrder = null; double bestScore = 0.;
            while (i.hasNext()) {
                Order o = (Order) i.next();
                if (trials.contains(o)) continue;
                OrderInfo score = (OrderInfo) infos.get(o);
                if (score != null && score.score < 0.05 && score.confidence >= 1.) {
                    continue;
                }
                score = orderGoodness(o);
                if (TRACE > 2) out.println(this+": "+score);
                if (score.score > bestScore) {
                    bestScore = score.score;
                    bestOrder = o;
                }
            }
            if (TRACE > 0) out.println(this+": best untried order "+bestOrder+" score "+format(bestScore));
            return bestOrder;
        }
        
        /* (non-Javadoc)
         * @see org.sf.bddbddb.FindBestDomainOrder.OrderInfoCollection#orderGoodness(org.sf.bddbddb.FindBestDomainOrder.Order)
         */
        public OrderInfo orderGoodness(Order o) {
            OrderInfo result = super.orderGoodness(o);
            OrderInfo predicted = trials.predict(o);
            if (TRACE > 1) out.print(this+": "+result+", trial score "+format(predicted.score)+" conf "+format(predicted.confidence));
            result.update(predicted);
            if (TRACE > 1) out.println(", total score "+format(result.score)+" conf "+format(result.confidence));
            return result;
        }
        
    }
    
    static BigInteger binomial(int n, int k) {
        BigInteger r = BigInteger.ONE;
        int n_minus_k = n-k;
        while (n > k) {
            r = r.multiply(BigInteger.valueOf(n--));
        }
        while (n_minus_k > 0) {
            r = r.divide(BigInteger.valueOf(n_minus_k--));
        }
        return r;
    }
    
    static BigInteger recurrence(int n) {
        if (n <= 1) return BigInteger.ONE;
        BigInteger sum = BigInteger.ZERO;
        for (int k = 1; k <= n; ++k) {
            sum = sum.add(binomial(n, k).multiply(recurrence(n-k)));
        }
        return sum;
    }
    
    public static void main(String[] args) {
        
        for (int i = 0; i < 20; ++i) {
            System.out.println("Recurrence A000670 ("+i+") = "+recurrence(i));
        }
        List orders = generateAllOrders(Arrays.asList(args));
        System.out.println("Number of orders: "+orders.size());
        Iterator i = getOrderIterator(Arrays.asList(args));
        int k = 0;
        while (i.hasNext()) {
            Order o = (Order) i.next();
            System.out.println((++k)+": "+o);
            boolean b = orders.remove(o);
            Assert._assert(b);
            if (false) {
                Iterator j = getOrderIterator(Arrays.asList(args));
                while (j.hasNext()) {
                    Order p = (Order) j.next();
                    System.out.print(" with "+p+" = ");
                    System.out.println(o.findSimilarities(p));
                }
            }
        }
        Assert._assert(orders.isEmpty());
    }
    
}
