// FindBestDomainOrder.java, created Aug 21, 2004 1:17:30 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.io.PrintStream;
import java.text.NumberFormat;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.EntryValueComparator;
import org.sf.bddbddb.util.Pair;
import org.sf.bddbddb.util.PermutationGenerator;

/**
 * FindBestDomainOrder
 * 
 * @author John Whaley
 * @version $Id$
 */
public class FindBestDomainOrder {
    
    public static int TRACE = 1;
    public static PrintStream out = System.out;
    
    Map/*<InferenceRule,OrderingInfo>*/ orderInfo_rules;
    Map/*<Relation,OrderingInfo>*/ orderInfo_relations;
    
    public static FindBestDomainOrder INSTANCE = new FindBestDomainOrder();
    
    /**
     * 
     */
    public FindBestDomainOrder() {
        super();
        orderInfo_rules = new HashMap();
        orderInfo_relations = new HashMap();
    }
    
    public OrderInfoCollection getOrderInfo(InferenceRule r) {
        OrderInfoCollection o = (OrderInfoCollection) orderInfo_rules.get(r);
        if (o == null) {
            if (TRACE > 0) out.println("Initializing new ordering info for "+r);
            orderInfo_rules.put(r, o = new OrderInfoCollection("rule"+r.id));
        }
        return o;
    }
    
    public OrderInfoCollection getOrderInfo(Relation r) {
        OrderInfoCollection o = (OrderInfoCollection) orderInfo_relations.get(r);
        if (o == null) {
            if (TRACE > 0) out.println("Initializing new ordering info for "+r);
            orderInfo_relations.put(r, o = new OrderInfoCollection(r.name));
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
    
    public interface OrderTranslator {
        Order translate(Order o);
    }
    
    public static class IdentityTranslator implements OrderTranslator {
        public static final IdentityTranslator INSTANCE = new IdentityTranslator();
        public Order translate(Order o) { return new Order(new LinkedList(o)); }
    }
    
    public static class MapBasedTranslator implements OrderTranslator {
        
        Map m;
        
        MapBasedTranslator(Map m) {
            this.m = m;
        }
        
        /**
         * direction == true means map from rule to relation.
         * direction == false means map from relation to rule.
         * 
         * @param ir
         * @param r
         * @param direction
         */
        MapBasedTranslator(InferenceRule ir, Relation r, boolean direction) {
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
        
        public Order translate(Order o) {
            LinkedList result = new LinkedList();
            for (Iterator i = o.iterator(); i.hasNext(); ) {
                Object a = i.next();
                Object b = m.get(a);
                //result.add(b != null ? b : a);
                if (b != null) result.add(b);
            }
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
            if (true)
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
        
        double similarity0(Order that) {
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
        
        public int compareTo(Object arg0) {
            return compareTo((Order) arg0);
        }
        public int compareTo(Order that) {
            return this.toString().compareTo(that.toString());
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
    
    static NumberFormat nf;
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
            if (this.confidence + that_confidence < 0.0001) return;
            double newScore = (this.score * this.confidence + that_score * that_confidence) /
                              (this.confidence + that_confidence);
            // todo: this confidence calculation seems bogus.
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
        String name;
        Map/*<Order,TrialInfo>*/ trials;
        transient TrialInfo[] sorted;
        
        public TrialCollection(String n) {
            name = n;
            trials = new LinkedHashMap();
            sorted = null;
        }
        
        public void addTrial(TrialInfo i) {
            if (TRACE > 1) out.println(this+": Adding trial "+i);
            trials.put(i.order, i);
            sorted = null;
        }
        public void addTrial(Order o, long cost) {
            addTrial(new TrialInfo(o, cost));
        }
        
        public boolean contains(Order o) {
            return trials.containsKey(o);
        }
        
        public OrderInfo predict(Order o) {
            OrderInfo result = (OrderInfo) trials.get(o);
            if (result != null) return result;
            if (TRACE > 2) out.println(this+": Predicting "+o);
            result = new OrderInfo(o, 0.5, 0.);
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
        
        public double getStdDev() {
            return Math.sqrt(getVariance());
        }
        
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
        
        public TrialInfo getMinimum() {
            TrialInfo best = null;
            for (Iterator i = trials.values().iterator(); i.hasNext(); ) {
                TrialInfo t = (TrialInfo) i.next();
                if (best == null || t.cost < best.cost)
                    best = t;
            }
            return best;
        }
        
        public TrialInfo getMaximum() {
            TrialInfo best = null;
            for (Iterator i = trials.values().iterator(); i.hasNext(); ) {
                TrialInfo t = (TrialInfo) i.next();
                if (best == null || t.cost > best.cost)
                    best = t;
            }
            return best;
        }
        
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
        
        public TrialInfo[] getSorted() {
            if (sorted == null) {
                sorted = (TrialInfo[]) trials.values().toArray(new TrialInfo[trials.size()]);
                Arrays.sort(sorted);
            }
            return sorted;
        }
        
        public int size() {
            return trials.size();
        }
        
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
        
        String name;
        Map/*<Order,OrderInfo>*/ infos;
        transient OrderInfo[] sorted;
        
        OrderInfoCollection(String s) {
            name = s;
            infos = new LinkedHashMap();
            sorted = null;
        }
        
        OrderInfoCollection(OrderInfoCollection that) {
            this.name = that.name;
            this.infos = new LinkedHashMap(that.infos);
            this.sorted = null;
        }
        
        public void incorporateInfoCollection(OrderInfoCollection that, double confidence) {
            incorporateInfoCollection(that, IdentityTranslator.INSTANCE, confidence);
        }
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
        
        public void incorporateTrials(TrialCollection c, double confidence) {
            incorporateTrials(c, IdentityTranslator.INSTANCE, confidence);
        }
        public void incorporateTrials(TrialCollection c, OrderTranslator t, double confidence) {
            if (c.size() > 0) {
                if (TRACE > 0) out.println(this+": incorporating trials "+c+" with confidence "+format(confidence));
                TrialInfo[] ti = c.getSorted();
                long min = ti[0].cost;
                long max = ti[ti.length-1].cost;
                double range = (double)max - (double)min;
                for (int i = 0; i < ti.length; ++i) {
                    Order o = t.translate(ti[i].order);
                    double score = (range < 0.0001) ? 0.5 : ((double)(max - ti[i].cost) / range);
                    double myConf = (range < 0.0001) ? 0. : confidence;
                    if (ti[i].cost >= UpdatableOrderInfoCollection.MAX_COST) myConf *= HIGH_CONFIDENCE;
                    incorporateInfo(o, score, myConf);
                }
            }
        }
        
        public void incorporateInfo(Order o, double s, double c) {
            OrderInfo info = (OrderInfo) infos.get(o);
            if (info == null) {
                infos.put(o, info = new OrderInfo(o, s, c));
                if (TRACE > 1) out.println(this+": incorporating new info "+info);
            } else {
                if (TRACE > 1) out.println(this+": updating info "+info+" with score="+format(s)+" confidence="+format(c));
                info.update(o, s, c);
            }
            sorted = null;
        }
        public void incorporateInfo(OrderInfo i) {
            OrderInfo info = (OrderInfo) infos.get(i.order);
            if (info == null) {
                infos.put(i.order, info = i);
                if (TRACE > 1) out.println(this+": incorporating new info "+info);
            } else {
                if (TRACE > 1) out.println(this+": updating info "+info+" with score="+format(i.score)+" confidence="+format(i.confidence));
                info.update(i);
            }
            sorted = null;
        }
        
        public OrderInfo getTotalOrderInfo(Order o) {
            return (OrderInfo) infos.get(o);
        }
        
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
        
        
        public UpdatableOrderInfoCollection createUpdatable() {
            UpdatableOrderInfoCollection i = new UpdatableOrderInfoCollection(this);
            return i;
        }
        
        static double HIGH_CONFIDENCE = 10000.;
        
        public void registerAsGood(Order o) {
            if (TRACE > 0) out.println(this+": Registering as a known good order: "+o);
            infos.put(o, new OrderInfo(o, 1., HIGH_CONFIDENCE));
            sorted = null;
        }
        
        public void registerAsBad(Order o) {
            if (TRACE > 0) out.println(this+": Registering as a known bad order: "+o);
            infos.put(o, new OrderInfo(o, 0., HIGH_CONFIDENCE));
            sorted = null;
        }
        
        public int numberOfGoodOrders(List/*<Variable>*/ variables) {
            OrderIterator i = generateAllOrders(variables);
            int count = 0;
            while (i.hasNext()) {
                Order o = i.nextOrder();
                OrderInfo score = orderGoodness(o);
                if (score.score > 0.05) {
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
            OrderIterator i = generateAllOrders(variables);
            Order bestOrder = null; double bestScore = 0.05;
            while (i.hasNext()) {
                Order o = i.nextOrder();
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
         * Return a measure of the probable "goodness" of the given order.
         * The number is between 0.0 and 1.0, with higher numbers being better.
         * 
         * @param o  order
         * @return  probable goodness
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
        
        OrderInfo[] getSorted() {
            if (sorted == null) {
                sorted = (OrderInfo[]) infos.values().toArray(new OrderInfo[infos.size()]);
                Arrays.sort(sorted);
            }
            return sorted;
        }
        
        Collection/*<OrderInfo>*/ goodCharacteristics;
        Collection/*<OrderInfo>*/ badCharacteristics;
        
        void calculateCharacteristics() {
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
            
            goodCharacteristics.clear();
            badCharacteristics.clear();
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
        
        TrialCollection trials;
        
        static long MIN_COST = 0L;
        static long MAX_COST = 10000000L;
        
        UpdatableOrderInfoCollection(String s) {
            super(s);
            trials = new TrialCollection(s);
        }
        
        UpdatableOrderInfoCollection(OrderInfoCollection that) {
            super(that);
            trials = new TrialCollection(that.name);
        }
        
        public void registerNewTrial(Order o, long cost) {
            if (cost >= MAX_COST) {
                registerAsBad(o);
                return;
            }
            if (TRACE > 0) out.println(this+": registering new raw data "+o+" score "+cost);
            TrialInfo i = new TrialInfo(o, cost);
            trials.addTrial(i);
        }
        
        public void registerAsGood(Order o) {
            super.registerAsGood(o);
            TrialInfo i = new TrialInfo(o, MIN_COST);
            trials.addTrial(i);
        }
        
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
            //calculateCharacteristics();
            // Find an order that has some of the good order characteristics
            // without any of the bad ones.
            if (TRACE > 0) out.println(this+": generating new orders for "+variables);
            OrderIterator i = generateAllOrders(variables);
            Order bestOrder = null; double bestScore = 0.05;
            while (i.hasNext()) {
                Order o = i.nextOrder();
                if (trials.contains(o)) continue;
                OrderInfo score = orderGoodness(o);
                if (TRACE > 2) out.println(this+": "+score);
                if (score.score > bestScore) {
                    bestScore = score.score;
                    bestOrder = o;
                }
            }
            if (TRACE > 0) out.println(this+": best untried order "+bestOrder+" score "+format(bestScore));
            return bestOrder;
        }
        
        public OrderInfo orderGoodness(Order o) {
            OrderInfo result = super.orderGoodness(o);
            OrderInfo predicted = trials.predict(o);
            if (TRACE > 2) out.print(this+": "+result+", trial score "+format(predicted.score)+" conf "+format(predicted.confidence));
            result.update(predicted);
            if (TRACE > 2) out.println(", total score "+format(result.score)+" conf "+format(result.confidence));
            return result;
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
