// FindBestDomainOrder.java, created Aug 21, 2004 1:17:30 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Writer;
import java.math.BigInteger;
import java.net.URL;
import java.text.NumberFormat;
import java.text.SimpleDateFormat;
import jwutil.collections.EntryValueComparator;
import jwutil.collections.Pair;
import jwutil.util.Assert;
import net.sf.bddbddb.order.IdentityTranslator;
import net.sf.bddbddb.order.Order;
import net.sf.bddbddb.order.OrderConstraint;
import net.sf.bddbddb.order.OrderIterator;
import net.sf.bddbddb.order.OrderTranslator;
import net.sf.bddbddb.order.PrecedenceConstraint;
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.input.SAXBuilder;
import org.jdom.output.Format;
import org.jdom.output.XMLOutputter;

/**
 * FindBestDomainOrder
 * 
 * Design:
 * 
 * TrialInfo : order, cost
 * TrialCollection : collection of TrialInfo, best time, worst time
 * Constraint: a<b or axb or a_b
 * Order : collection of ordering constraints
 * ConstraintInfo : map from a single constraint to score/confidence
 * OrderInfo : order, predicted score and confidence
 * 
 * Maps:
 *  Relation -> ConstraintInfo collection
 *  Rule -> ConstraintInfo collection
 *  TrialCollection -> ConstraintInfo collection
 * 
 * Algorithm to compute best order:
 * - Combine and sort single constraints from relation, rule, trials so far.
 *   Sort by score*confidence (?)
 *   Combine and adjust opposite constraints (?)
 *   Sort by difference between opposite constraints (?)
 * - Do an A* search.
 *   Keep track of the current score/confidence as we add constraints.
 *   As we add new constraints, flag conflicting ones.
 *   Predict final score by combining top n non-conflicting constraints (?)
 *   If prediction is worse than current best score, return immediately.
 * 
 * @author John Whaley
 * @version $Id$
 */
public class FindBestDomainOrder {
    
    public static int TRACE = 2;
    public static PrintStream out = System.out;
    
    static final SimpleDateFormat dateFormat = new SimpleDateFormat("yyMMdd-HHmmss");
    
    Map/*<InferenceRule,OrderInfoCollection>*/ orderInfo_rules;
    Map/*<Relation,OrderInfoCollection>*/ orderInfo_relations;
    
    /**
     * Collection of all TrialCollections that have been done so far, including
     * ones that have been loaded from disk.
     */
    Collection allTrials;
    
    /**
     * Link back to the solver.
     */
    Solver solver;
    
    /**
     * Construct a new empty FindBestDomainOrder object.
     */
    public FindBestDomainOrder(Solver s) {
        super();
        orderInfo_rules = new HashMap();
        orderInfo_relations = new HashMap();
        allTrials = new LinkedList();
        solver = s;
    }
    
    /**
     * Load and incorporate trials from the given XML file.
     * 
     * @param filename  filename
     */
    void loadTrials(String filename) {
        File file = new File(filename);
        if (file.exists()) {
            try {
                URL url = file.toURL();
                SAXBuilder builder = new SAXBuilder();
                Document doc = builder.build(url);
                XMLFactory f = new XMLFactory(solver);
                Element e = doc.getRootElement();
                List list = (List) f.fromXML(e);
                if (TRACE > 0) {
                    out.println("Loaded "+list.size()+" trial collections from file.");
                    if (TRACE > 1) {
                        for (Iterator i = list.iterator(); i.hasNext(); ) {
                            out.println("Loaded from file: "+i.next());
                        }
                    }
                }
                allTrials.addAll(list);
            } catch (Exception e) {
                System.err.println("Error occurred loading "+filename+": "+e);
                e.printStackTrace();
            }
        }
        incorporateTrials();
    }
    
    void incorporateTrials() {
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection tc = (TrialCollection) i.next();
            InferenceRule ir = tc.getRule(solver);
            OrderInfoCollection ruleinfo = getOrderInfo(ir);
            TrialInfo ti = tc.getMinimum();
            if (ti != null) {
                double confidence = (double) ti.cost / 1000.;
                ruleinfo.incorporateTrials(tc, confidence, true);
            }
        }
    }
    
    /**
     * Construct a new FindBestDomainOrder object with the given info.
     * 
     * @param m1  map from rules to their info
     * @param m2  map from relations to their info
     */
    FindBestDomainOrder(Map/*<InferenceRule,OrderInfoCollection>*/ m1,
                        Map/*<Relation,OrderInfoCollection>*/ m2) {
        super();
        orderInfo_rules = m1;
        orderInfo_relations = m2;
        allTrials = new LinkedList();
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
            System.out.println("Rule: "+ir);
            OrderInfoCollection info = (OrderInfoCollection)e.getValue();
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
     * Information about a particular constraint.
     * 
     * @author jwhaley
     * @version $Id$
     */
    public static class ConstraintInfo {
        
        OrderConstraint c;
        double score;
        double confidence;
        
        /**
         * Construct a new ConstraintInfo.
         * 
         * @param c  constraint
         * @param score  score
         * @param confidence  confidence
         */
        public ConstraintInfo(OrderConstraint c, double score, double confidence) {
            super();
            this.c = c;
            this.score = score;
            this.confidence = confidence;
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return c+": score "+format(score)+" confidence "+format(confidence);
        }
        
    }
    
    /**
     * Generate all orders of a given list of variables.
     * 
     * @param vars  list of variables
     * @return  list of all orders of those variables
     */
    public static List/*<OrderInfo>*/ generateOrders(List vars,
        double bestScore, ConstraintInfoCollection constraints) {
        if (vars.size() == 0) return null;
        LinkedList result = new LinkedList();
        if (vars.size() == 1) {
            Order o = new Order(vars);
            OrderInfo oi = new OrderInfo(o, .5, 0);
            result.add(oi);
            return result;
        }
        
        // Get the answers for the rest of the list.
        List recurse = generateAllOrders(vars.subList(1, vars.size()));
        
        // Precompute the individual scores for precedence constraints.
        Iterator it = vars.iterator();
        Object car = it.next();
        ArrayList/*<OrderInfo>*/ beforeConstraints = new ArrayList(vars.size()-1);
        ArrayList/*<OrderInfo>*/ afterConstraints = new ArrayList(vars.size()-1);
        while (it.hasNext()) {
            Object cadr = it.next();
            PrecedenceConstraint before = new PrecedenceConstraint(car, cadr);
            ConstraintInfo before_i = constraints.getInfo(before);
            beforeConstraints.add(before_i);
            PrecedenceConstraint after = new PrecedenceConstraint(cadr, car);
            ConstraintInfo after_i = constraints.getInfo(after);
            afterConstraints.add(after_i);
        }
        
        // Try placing the new element inbetween each of the elements.
        for (Iterator i = recurse.iterator(); i.hasNext(); ) {
            OrderInfo oi = (OrderInfo) i.next();
            Order order = oi.order;
            OrderInfo order_result = new OrderInfo(oi);
            for (Iterator j = order.iterator(); j.hasNext(); ) {
                Object cadr = j.next();
                Collection c = (cadr instanceof Collection) ? ((Collection) cadr) : Collections.singleton(cadr);
                for (Iterator k = c.iterator(); k.hasNext(); ) {
                    Object o = k.next();
                    int index = vars.indexOf(o);
                    ConstraintInfo oi2 = (ConstraintInfo) beforeConstraints.get(index-1);
                    order_result.update(oi2);
                }
            }
            List newOrderList = new ArrayList(order.size() + 1);
            newOrderList.add(car);
            newOrderList.addAll(order);
            OrderInfo order_result2 = new OrderInfo(new Order(newOrderList), order_result.score, order_result.confidence);
            result.add(order_result2);
            for (Iterator j = order.iterator(); j.hasNext(); ) {
                Object cadr = j.next();
                Collection c = (cadr instanceof Collection) ? ((Collection) cadr) : Collections.singleton(cadr);
                for (Iterator k = c.iterator(); k.hasNext(); ) {
                    Object o = k.next();
                    int index = vars.indexOf(o);
                    ConstraintInfo oi2 = (ConstraintInfo) beforeConstraints.get(index-1);
                    order_result.unupdate(oi2);
                    ConstraintInfo oi3 = (ConstraintInfo) afterConstraints.get(index-1);
                    order_result.update(oi3);
                }
                newOrderList = new ArrayList(order.size() + 1);
                for (Iterator m = order.iterator(); m.hasNext(); ) {
                    Object o = m.next();
                    newOrderList.add(o);
                    if (o == cadr) {
                        newOrderList.add(car);
                    }
                }
                order_result2 = new OrderInfo(new Order(newOrderList), order_result.score, order_result.confidence);
                result.add(order_result2);
            }
        }
        
        // Try placing the new element with each of the elements.
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
    
    transient static NumberFormat nf;
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
        
        public void update(ConstraintInfo info) {
            update(info.score, info.confidence);
        }
        
        /**
         * Update the score and confidence to take into account another order info.
         * Assumes that the two are referring to the same order.
         * 
         * @param that  order to incorporate
         */
        public void update(OrderInfo that) {
            update(that.score, that.confidence);
        }
        public void update(double that_score, double that_confidence) {
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
        
        public void unupdate(ConstraintInfo that) {
            update(that.score, that.confidence);
        }
        public void unupdate(double that_score, double that_confidence) {
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
            if (this == that) return 0;
            int result = signum(this.score - that.score);
            if (result == 0) {
                result = (int) signum(this.confidence - that.confidence);
                if (result == 0) {
                    result = this.order.compareTo(that.order);
                }
            }
            return result;
        }
        
        /**
         * Returns this OrderInfo as an XML element.
         * 
         * @return  XML element
         */
        public Element toXMLElement() {
            Element dis = new Element("orderInfo");
            dis.setAttribute("order", order.toString());
            dis.setAttribute("score", Double.toString(score));
            dis.setAttribute("confidence", Double.toString(confidence));
            return dis;
        }
        
        public static OrderInfo fromXMLElement(Element e, Map nameToVar) {
            Order o = Order.parse(e.getAttributeValue("order"), nameToVar);
            double s = Double.parseDouble(e.getAttributeValue("score"));
            double c = Double.parseDouble(e.getAttributeValue("confidence"));
            return new OrderInfo(o, s, c);
        }
    }
    
    // Only present in JDK1.5
    static int signum(long d) {
        if (d < 0) return -1;
        if (d > 0) return 1;
        return 0;
    }
    
    // Only present in JDK1.5
    static int signum(double d) {
        if (d < 0) return -1;
        if (d > 0) return 1;
        return 0;
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
            if (this == that) return 0;
            int result = signum(this.cost - that.cost);
            if (result == 0) {
                result = this.order.compareTo(that.order);
            }
            return result;
        }
        
        /**
         * Returns this TrialInfo as an XML element.
         * 
         * @return  XML element
         */
        public Element toXMLElement() {
            Element dis = new Element("trialInfo");
            dis.setAttribute("order", order.toString());
            dis.setAttribute("cost", Long.toString(cost));
            return dis;
        }
        
        public static TrialInfo fromXMLElement(Element e, Map nameToVar) {
            Order o = Order.parse(e.getAttributeValue("order"), nameToVar);
            long c = Long.parseLong(e.getAttributeValue("cost"));
            return new TrialInfo(o, c);
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
         * Time of the test.
         */
        long timeStamp;
        
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
        public TrialCollection(String n, long ts) {
            name = n;
            timeStamp = ts;
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
                    result.update(score, (range < 0.0001) ? 0. : sim);
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
            return name+"@"+dateFormat.format(new Date(timeStamp));
        }
        
        /**
         * Returns this TrialCollection as an XML element.
         * 
         * @return  XML element
         */
        public Element toXMLElement() {
            Element dis = new Element("trialCollection");
            dis.setAttribute("name", name);
            dis.setAttribute("timeStamp", Long.toString(timeStamp));
            for (Iterator i = trials.values().iterator(); i.hasNext(); ) {
                TrialInfo info = (TrialInfo) i.next();
                dis.addContent(info.toXMLElement());
            }
            return dis;
        }
        
        static InferenceRule parseRule(Solver solver, String s) {
            int ruleNum = Integer.parseInt(s.substring(4));
            InferenceRule rule = (InferenceRule) solver.rules.get(ruleNum);
            return rule;
        }
        
        public InferenceRule getRule(Solver solver) {
            return parseRule(solver, name);
        }
        
        public static TrialCollection fromXMLElement(Element e, Solver solver) {
            String name = e.getAttributeValue("name");
            InferenceRule rule = parseRule(solver, name);
            Map nameToVar = rule.getVarNameMap();
            long timeStamp;
            try {
                timeStamp = Long.parseLong(e.getAttributeValue("timeStamp"));
            } catch (NumberFormatException _) {
                timeStamp = 0L;
            }
            TrialCollection tc = new TrialCollection(name, timeStamp);
            for (Iterator i = e.getContent().iterator(); i.hasNext(); ) {
                Object e2 = i.next();
                if (e2 instanceof Element) {
                    TrialInfo ti = TrialInfo.fromXMLElement((Element) e2, nameToVar);
                    tc.addTrial(ti);
                }
            }
            return tc;
        }
    }
    
    public static class ConstraintInfoCollection {
        
        /**
         * Map from orders to their info.
         */
        Map/*<OrderConstraint,ConstraintInfo>*/ infos;
        
        public ConstraintInfo getInfo(OrderConstraint c) {
            return (ConstraintInfo) infos.get(c);
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
        
        transient OrderClassifier classifier;
        
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
            classifier = null;
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
            this.classifier = null;
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
        public void incorporateTrials(TrialCollection c, double confidence, boolean boostConfidence) {
            incorporateTrials(c, IdentityTranslator.INSTANCE, confidence, boostConfidence);
        }
        
        /**
         * Incorporate trials into this info collection using the given confidence
         * rating for the trials, translating orders with the given translator. 
         * 
         * @param c  trial collection to incorporate
         * @param t  order translator
         * @param confidence  confidence rating for trials
         * @param boostConfidence  boost confidence for trials with cost greater than MAX_COST
         */
        public void incorporateTrials(TrialCollection c, OrderTranslator t, double confidence,
                                      boolean boostConfidence) {
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
                    if (boostConfidence && isNew && ti[i].cost >= UpdatableOrderInfoCollection.MAX_COST) {
                        myConf *= HIGH_CONFIDENCE;
                        if (TRACE > 1) out.println(this+": new max_cost trial, boosting confidence to "+myConf);
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
                info.update(s, c);
            }
            if (false) {
                for (Iterator i = infos.values().iterator(); i.hasNext(); ) {
                    OrderInfo info2 = (OrderInfo) i.next();
                    if (info == info2) continue;
                    if (o.similarity(info2.order) >= 1.0) {
                        if (TRACE > 1) out.println(this+": updating info "+info2+" with score="+format(s)+" confidence="+format(c));
                        info2.update(s, c);
                    }
                }
            }
            sorted = null;
            classifier = null;
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
            classifier = null;
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
            long timeStamp = System.currentTimeMillis();
            UpdatableOrderInfoCollection i = new UpdatableOrderInfoCollection(this, timeStamp);
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
            classifier = null;
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
            classifier = null;
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
            OrderClassifier c = getOrderClassifier();
            Iterator i = generateAllOrders(variables).iterator();
            // Find the order with the highest score.
            // todo: should be also consider the confidence?
            Order bestOrder = null; double bestScore = 0.;
            while (i.hasNext()) {
                Order o = (Order) i.next();
                OrderInfo score = c.orderGoodness(o);
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
        
        public OrderClassifier getOrderClassifier() {
            if (classifier == null) {
                classifier = new FastOrderClassifier(this);
            }
            return classifier;
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
            Map/*<Order,Integer>*/ goodSim = Order.calcLongSimilarities(good);
            Map/*<Order,Integer>*/ badSim = Order.calcLongSimilarities(bad);
            
            Map.Entry[] sortedGoodSim = (Map.Entry[]) goodSim.entrySet().toArray(new Map.Entry[goodSim.size()]);
            Arrays.sort(sortedGoodSim, EntryValueComparator.INSTANCE);
            if (TRACE > 0) out.println(this+": similarities of good set: "+Arrays.asList(sortedGoodSim));
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
        
        /**
         * Returns this OrderInfoCollection as an XML element.
         * 
         * @return  XML element
         */
        public Element toXMLElement() {
            Element dis = new Element("orderInfoCollection");
            dis.setAttribute("name", name);
            OrderInfo[] s = getSorted();
            for (int i = 0; i < s.length; ++i) {
                Element e = s[i].toXMLElement();
                dis.addContent(e);
            }
            return dis;
        }
        
        public static OrderInfoCollection fromXMLElement(Element e, Map nameToVar) {
            String name = e.getAttributeValue("name");
            OrderInfoCollection oc = new OrderInfoCollection(name);
            for (Iterator i = e.getContent().iterator(); i.hasNext(); ) {
                Object e2 = i.next();
                if (e2 instanceof Element) {
                    OrderInfo oi = OrderInfo.fromXMLElement((Element) e2, nameToVar);
                    oc.infos.put(oi.order, oi);
                }
            }
            return oc;
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
        UpdatableOrderInfoCollection(String s, long timeStamp) {
            super(s);
            trials = new TrialCollection(s, timeStamp);
        }
        
        UpdatableOrderInfoCollection(OrderInfoCollection that, long timeStamp) {
            super(that);
            trials = new TrialCollection(that.name, timeStamp);
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
         * @see net.sf.bddbddb.FindBestDomainOrder.OrderInfoCollection#registerAsGood(net.sf.bddbddb.FindBestDomainOrder.Order)
         */
        public void registerAsGood(Order o) {
            super.registerAsGood(o);
            TrialInfo i = new TrialInfo(o, MIN_COST);
            trials.addTrial(i);
        }
        
        /* (non-Javadoc)
         * @see net.sf.bddbddb.FindBestDomainOrder.OrderInfoCollection#registerAsBad(net.sf.bddbddb.FindBestDomainOrder.Order)
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
            OrderClassifier c = getOrderClassifier();
            // Find the order with the highest score that we haven't tried yet
            // and that is still possibly good.
            // todo: should be also consider the confidence?
            long time = System.currentTimeMillis();
            Iterator i = generateAllOrders(variables).iterator();
            Order bestOrder = null; double bestScore = 0.;
            while (i.hasNext()) {
                Order o = (Order) i.next();
                if (trials.contains(o)) continue;
                OrderInfo score = (OrderInfo) infos.get(o);
                if (score != null && score.score < 0.05 && score.confidence >= 1.) {
                    continue;
                }
                score = c.orderGoodness(o);
                if (TRACE > 2) out.println(this+": "+score);
                if (score.score > bestScore) {
                    bestScore = score.score;
                    bestOrder = o;
                }
            }
            if (TRACE > 0) out.println(this+": best untried order "+bestOrder+" score "+format(bestScore));
            if (TRACE > 0) out.println(this+": finding best untried order took "+(System.currentTimeMillis()-time)+" ms");
            return bestOrder;
        }
        
        public OrderClassifier getOrderClassifier() {
            if (!(classifier instanceof UpdatableOrderClassifier)) {
                classifier = new UpdatableOrderClassifier(this);
            }
            return classifier;
        }
        
    }
    
    public interface OrderClassifier {
        
        /**
         * Return a measure of the probable "goodness" of the given order, and
         * a confidence of that score.
         * The score is between 0.0 and 1.0, with higher numbers being better.
         * If we already have info about a given order, use it.
         * 
         * @param o  order
         * @return  probable goodness and confidence of that rating
         */
        OrderInfo orderGoodness(Order o);
        
    }
    
    public static class UpdatableOrderClassifier extends FastOrderClassifier {
        
        //Map/*<Pair,OrderInfo>*/ precedence2;
        //Map/*<Pair,OrderInfo>*/ interleave2;
        
        /**
         * 
         */
        public UpdatableOrderClassifier(UpdatableOrderInfoCollection c) {
            super(c);
        }
        
        /* (non-Javadoc)
         * @see net.sf.bddbddb.FindBestDomainOrder.OrderClassifier#orderGoodness(net.sf.bddbddb.FindBestDomainOrder.Order)
         */
        public OrderInfo orderGoodness(Order o) {
            OrderInfo result = super.orderGoodness(o);
            OrderInfo predicted = ((UpdatableOrderInfoCollection) c).trials.predict(o);
            if (TRACE > 1) out.print(c+": "+result+", trial score "+format(predicted.score)+" conf "+format(predicted.confidence));
            result.update(predicted);
            if (TRACE > 1) out.println(", total score "+format(result.score)+" conf "+format(result.confidence));
            return result;
        }
        
    }
    
    public static class FastOrderClassifier implements OrderClassifier {
        
        OrderInfoCollection c;
        Map/*<Pair,OrderInfo>*/ precedence;
        Map/*<Pair,OrderInfo>*/ interleave;
        double totalPredConf;
        double totalInterConf;
        
        private void incorporate(Map m, Pair p, OrderInfo new_oi, boolean interleave) {
            OrderInfo oi = (OrderInfo) m.get(p);
            if (oi == null) {
                Order o = new Order(interleave?Collections.singletonList(p):p);
                m.put(p, oi = new OrderInfo(o, new_oi.score, new_oi.confidence));
            } else {
                oi.update(new_oi);
            }
        }
        
        public FastOrderClassifier(OrderInfoCollection c) {
            this.c = c;
            this.precedence = new HashMap();
            this.interleave = new HashMap();
            for (Iterator i = c.infos.values().iterator(); i.hasNext(); ) {
                OrderInfo info = (OrderInfo) i.next();
                Collection ps = info.order.getAllPrecedenceConstraints();
                for (Iterator j = ps.iterator(); j.hasNext(); ) {
                    Pair p = (Pair) j.next();
                    incorporate(precedence, p, info, false);
                }
                Collection is = info.order.getAllInterleaveConstraints();
                for (Iterator j = is.iterator(); j.hasNext(); ) {
                    Pair p = (Pair) j.next();
                    incorporate(interleave, p, info, true);
                }
            }
            totalPredConf = 0.;
            for (Iterator i = precedence.values().iterator(); i.hasNext(); ) {
                OrderInfo oi = (OrderInfo) i.next();
                totalPredConf += oi.confidence;
            }
            totalInterConf = 0.;
            for (Iterator i = interleave.values().iterator(); i.hasNext(); ) {
                OrderInfo oi = (OrderInfo) i.next();
                totalInterConf += oi.confidence;
            }
            if (TRACE > 1) {
                dumpInfo();
            }
        }
        
        public void dumpInfo() {
            List infos = new ArrayList(precedence.size() + interleave.size());
            infos.addAll(precedence.values());
            infos.addAll(interleave.values());
            OrderInfo[] sorted = (OrderInfo[]) infos.toArray(new OrderInfo[infos.size()]);
            Arrays.sort(sorted);
            int num = Math.min(5, sorted.length/2);
            if (num > 0) {
                out.println(c+": Best constraints:");
                for (int i = 0; i < num; ++i) {
                    out.println(sorted[sorted.length-i-1]);
                }
                out.println(c+": Worst constraints:");
                for (int i = 0; i < num; ++i) {
                    out.println(sorted[i]);
                }
            }
        }
        
        public OrderInfo orderGoodness(Order o) {
            OrderInfo result = (OrderInfo) c.infos.get(o);
            if (result != null) return result;
            
            if (TRACE > 2) out.print(c+": Calculating goodness of "+o);
            double score = 0.;
            double resultScore;
            double total = Order.PRECEDENCE_WEIGHT*totalPredConf +
                           Order.INTERLEAVE_WEIGHT*totalInterConf;
            if (total > 0.0001) {
                Collection ps = o.getAllPrecedenceConstraints();
                for (Iterator j = ps.iterator(); j.hasNext(); ) {
                    Pair p = (Pair) j.next();
                    OrderInfo oi = (OrderInfo) precedence.get(p);
                    if (oi != null) {
                        score += oi.score * oi.confidence * Order.PRECEDENCE_WEIGHT;
                    }
                }
                Collection is = o.getAllInterleaveConstraints();
                for (Iterator j = is.iterator(); j.hasNext(); ) {
                    Pair p = (Pair) j.next();
                    OrderInfo oi = (OrderInfo) interleave.get(p);
                    if (oi != null) {
                        score += oi.score * oi.confidence * Order.INTERLEAVE_WEIGHT;
                    }
                }
                resultScore = score / total;
            } else {
                resultScore = 0.5;
            }
            
            double resultConfidence = 0.;
            double scale = Order.INTERLEAVE_WEIGHT / (Order.PRECEDENCE_WEIGHT + Order.INTERLEAVE_WEIGHT);
            Collection ps = o.getAllPrecedenceConstraints();
            for (Iterator j = ps.iterator(); j.hasNext(); ) {
                Pair p = (Pair) j.next();
                OrderInfo oi = (OrderInfo) precedence.get(p);
                if (oi != null) {
                    double howConfident = oi.confidence * scale;
                    double diff = (oi.score - resultScore);
                    double diffSquared = diff * diff;
                    resultConfidence = (resultConfidence + howConfident) / (diffSquared + 1.);
                }
            }
            scale = 1 - scale;
            Collection is = o.getAllInterleaveConstraints();
            for (Iterator j = is.iterator(); j.hasNext(); ) {
                Pair p = (Pair) j.next();
                OrderInfo oi = (OrderInfo) interleave.get(p);
                if (oi != null) {
                    double howConfident = oi.confidence * scale;
                    double diff = (oi.score - resultScore);
                    double diffSquared = diff * diff;
                    resultConfidence = (resultConfidence + howConfident) / (diffSquared + 1.);
                }
            }
            
            result = new OrderInfo(o, resultScore, resultConfidence);
            if (TRACE > 2) out.println(" = score "+format(resultScore)+" confidence "+format(resultConfidence));
            return result;
        }
    }
    
    public static class SlowOrderClassifier implements OrderClassifier {
        
        OrderInfoCollection c;
        
        public SlowOrderClassifier(OrderInfoCollection c) {
            this.c = c;
        }
        
        static OrderInfo orderGoodness(OrderInfoCollection c, Order o) {
            OrderInfo result = (OrderInfo) c.infos.get(o);
            if (result != null) return result;

            if (TRACE > 2) out.print(c+": Calculating goodness of "+o);
            double score = 0.;
            double max = 0.;
            for (Iterator i = c.infos.values().iterator(); i.hasNext(); ) {
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
            for (Iterator i = c.infos.values().iterator(); i.hasNext(); ) {
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
         * Return a measure of the probable "goodness" of the given order, and
         * a confidence of that score.
         * The score is between 0.0 and 1.0, with higher numbers being better.
         * If we already have info about a given order, use it.
         * 
         * @param o  order
         * @return  probable goodness and confidence of that rating
         */
        public OrderInfo orderGoodness(Order o) {
            return orderGoodness(c, o);
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
                    System.out.println(o.findLongSimilarities(p));
                }
            }
        }
        Assert._assert(orders.isEmpty());
    }
    
    /**
     * Returns this FindBestDomainOrder as an XML element.
     * 
     * @return  XML element
     */
    public Element toXMLElement() {
        Element ruleInfoCollection = new Element("ruleInfoCollection");
        for (Iterator i = orderInfo_rules.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry) i.next();
            InferenceRule ir = (InferenceRule) e.getKey();
            OrderInfoCollection c = (OrderInfoCollection) e.getValue();
            
            Element ruleInfo = new Element("ruleInfo");
            ruleInfo.setAttribute("rule", "rule"+ir.id);
            
            Element oic = c.toXMLElement();
            ruleInfo.addContent(oic);
            
            ruleInfoCollection.addContent(ruleInfo);
        }
        
        Element relationInfoCollection = new Element("relationInfoCollection");
        for (Iterator i = orderInfo_relations.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry) i.next();
            Relation r = (Relation) e.getKey();
            OrderInfoCollection c = (OrderInfoCollection) e.getValue();
            
            Element relationInfo = new Element("relationInfo");
            relationInfo.setAttribute("relation", r.name);
            
            Element oic = c.toXMLElement();
            relationInfo.addContent(oic);
            
            relationInfoCollection.addContent(relationInfo);
        }
        
        Element fbo = new Element("findBestOrder");
        fbo.addContent(ruleInfoCollection);
        fbo.addContent(relationInfoCollection);
        
        return fbo;
    }
    
    public static void dumpXML(String filename, Element e) {
        Writer w = null;
        try {
            w = new BufferedWriter(new FileWriter(filename)); 
            dumpXML(w, e);
            w.close();
        } catch (IOException x) {
            System.err.println("Error writing "+filename+": "+x);
            x.printStackTrace();
        } finally {
            try { if (w != null) w.close(); } catch (IOException _) { }
        }
    }
    
    /**
     * Dumps the given element as an XML document to the given writer.
     * 
     * @param out  output writer
     * @param e  element to write
     */
    public static void dumpXML(Writer out, Element e) throws IOException {
        Document d = new Document(e);
        XMLOutputter serializer = new XMLOutputter();
        serializer.setFormat(Format.getPrettyFormat());
        serializer.output(d, out);
    }
    
    public static class XMLFactory {
        
        Solver solver;
        
        XMLFactory(Solver s) {
            solver = s;
        }
        
        public InferenceRule getRule(String s) {
            return (InferenceRule) solver.rules.get(Integer.parseInt(s.substring(4)));
        }
        
        public Relation getRelation(String s) {
            return (Relation) solver.nameToRelation.get(s);
        }
        
        public InferenceRule ruleFromXML(Element e) {
            return (InferenceRule) solver.rules.get(Integer.parseInt(e.getText().substring(4)));
        }
        
        public Relation relationFromXML(Element e) {
            return (Relation) solver.nameToRelation.get(e.getText());
        }
        
        public Object fromXML(Element e) {
            String name = e.getName();
            Object o;
            if (name.equals("trialCollections")) {
                String fn = e.getAttributeValue("datalog");
                List results = new LinkedList();
                if (fn.equals(solver.inputFilename)) {
                    for (Iterator i = e.getContent().iterator(); i.hasNext(); ) {
                        Object q = i.next();
                        if (q instanceof Element) {
                            Element e2 = (Element) q;
                            if (e2.getName().equals("trialCollection")) {
                                results.add(fromXML(e2));
                            }
                        }
                    }
                }
                o = results;
            } else if (name.equals("trialCollection")) {
                TrialCollection tc = TrialCollection.fromXMLElement(e, solver);
                o = tc;
            } else if (name.equals("findBestOrder")) {
                Map m1 = null;
                Map m2 = null;
                for (Iterator i = e.getContent().iterator(); i.hasNext(); ) {
                    Object q = i.next();
                    if (q instanceof Element) {
                        Element e2 = (Element) q;
                        if (e2.getName().equals("ruleInfoCollection")) {
                            m1 = (Map) fromXML(e2);
                        } else if (e2.getName().equals("relationInfoCollection")) {
                            m2 = (Map) fromXML(e2);
                        }
                    }
                }
                if (m1 == null) m1 = new HashMap();
                if (m2 == null) m2 = new HashMap();
                o = new FindBestDomainOrder(m1, m2);
            } else if (name.equals("rule")) {
                o = ruleFromXML(e);
            } else if (name.equals("relation")) {
                o = relationFromXML(e);
            } else if (name.equals("ruleInfo")) {
                Element e0 = (Element) e.getContent(0);
                Element e1 = (Element) e.getContent(1);
                InferenceRule ir = ruleFromXML(e0);
                Map/*<String,Variable>*/ nameToVar = ir.getVarNameMap();
                OrderInfoCollection oic = OrderInfoCollection.fromXMLElement(e1, nameToVar);
                o = new Pair(ir, oic);
            } else if (name.equals("relationInfo")) {
                Element e0 = (Element) e.getContent(0);
                Element e1 = (Element) e.getContent(1);
                Relation r = relationFromXML(e0);
                Map/*<String,Attribute>*/ nameToVar = r.getAttribNameMap();
                OrderInfoCollection oic = OrderInfoCollection.fromXMLElement(e1, nameToVar);
                o = new Pair(r, oic);
            } else if (name.equals("ruleInfoCollection")) {
                Map result = new HashMap();
                for (Iterator i = e.getContent().iterator(); i.hasNext(); ) {
                    Object q = i.next();
                    if (q instanceof Element) {
                        Element e2 = (Element) q;
                        if (e2.getName().equals("ruleInfo")) {
                            InferenceRule ir = getRule(e2.getAttributeValue("rule"));
                            OrderInfoCollection oic = OrderInfoCollection.fromXMLElement(e2, ir.getVarNameMap());
                            result.put(ir, oic);
                        }
                    }
                }
                o = result;
            } else if (name.equals("relationInfoCollection")) {
                Map result = new HashMap();
                for (Iterator i = e.getContent().iterator(); i.hasNext(); ) {
                    Object q = i.next();
                    if (q instanceof Element) {
                        Element e2 = (Element) q;
                        if (e2.getName().equals("relationInfo")) {
                            Relation r = getRelation(e2.getAttributeValue("relation"));
                            OrderInfoCollection oic = OrderInfoCollection.fromXMLElement(e2, r.getAttribNameMap());
                            result.put(r, oic);
                        }
                    }
                }
                o = result;
            } else {
                throw new IllegalArgumentException("Cannot parse XML element "+name);
            }
            return o;
        }
        
    }
    
    /**
     * Returns the set of all trials performed so far as an XML element.
     * 
     * @return  XML element
     */
    public Element trialsToXMLElement() {
        Element trialCollections = new Element("trialCollections");
        if (solver.inputFilename != null)
            trialCollections.setAttribute("datalog", solver.inputFilename);
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection c = (TrialCollection) i.next();
            trialCollections.addContent(c.toXMLElement());
        }
        return trialCollections;
    }
}
