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
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Writer;
import java.net.URL;
import java.text.NumberFormat;
import java.text.SimpleDateFormat;
import jwutil.util.Assert;
import net.sf.bddbddb.order.InterleaveConstraint;
import net.sf.bddbddb.order.NotInterleaveConstraint;
import net.sf.bddbddb.order.Order;
import net.sf.bddbddb.order.OrderConstraint;
import net.sf.bddbddb.order.OrderIterator;
import net.sf.bddbddb.order.OrderTranslator;
import net.sf.bddbddb.order.PrecedenceConstraint;
import net.sf.bddbddb.order.VarToAttribTranslator;
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
    
    /**
     * Link back to the solver.
     */
    Solver solver;
    
    /**
     * Collection of all TrialCollections that have been done so far, including
     * ones that have been loaded from disk.
     */
    Collection allTrials;
    
    public static boolean PER_RULE_CONSTRAINTS = true;
    
    /**
     * Collection of the info for each of the constraints.
     */
    ConstraintInfoCollection constraintInfo;
    
    /**
     * Construct a new empty FindBestDomainOrder object.
     */
    public FindBestDomainOrder(Solver s) {
        constraintInfo = new ConstraintInfoCollection();
        allTrials = new LinkedList();
        solver = s;
    }
    
    /**
     * Construct a new FindBestDomainOrder object with the given info.
     */
    FindBestDomainOrder(ConstraintInfoCollection c) {
        constraintInfo = c;
        allTrials = new LinkedList();
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
            constraintInfo.addTrials(tc);
        }
    }
    
    /**
     * Dump the collected order info for rules and relations to standard output.
     */
    public void dump() {
        for (Iterator i = constraintInfo.infos.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry) i.next();
            OrderConstraint ir = (OrderConstraint) e.getKey();
            System.out.println("Order feature: "+ir);
            ConstraintInfo info = (ConstraintInfo) e.getValue();
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
        
        // Student-t test: requires both populations have equal means and
        // both distributions are normally distributed with equal variances
        
        // The usual models for confidence intervals:
        //    t tests, ANOVA, linear or curvilinear regression
        // These all require the following assumptions:
        //    independence of observations
        //    normality of sampling distribution
        //    uniformity of residuals
        
        /**
         * The constraint that this info is about.
         */
        OrderConstraint c;
        
        /**
         * The collection of trials that are used in the computation of the score.
         */
        Collection trials;
        
        /*** The rest of the fields are computed based on the trials. ***/
        
        double sumCost;
        double sumMinimumCost;
        double sumNormalizedCost;
        double sumNormalizedCostSq;
        int numTrials;
        
        /**
         * Construct a new ConstraintInfo.
         * 
         * @param c  constraint
         */
        public ConstraintInfo(OrderConstraint c) {
            this.c = c;
            this.trials = new LinkedList();
            this.sumCost = 0.;
            this.sumMinimumCost = 0.;
            this.sumNormalizedCost = 0.;
            this.sumNormalizedCostSq = 0.;
            this.numTrials = 0;
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return c+": score "+format(getMean())+" +- "+format(getConfidenceInterval(.1));
        }
        
        /**
         * A measure of, when using an order with this constraint, how long
         * the operation would take versus the best time for that operation.
         * For example, a score of 2 would mean that on average, orders with
         * this constraint took twice as long on an operation as the best
         * known order for that operation.
         * 
         * Obviously, the best possible score is 1, and lower numbers are better.
         */
        public double getMean() {
            return sumNormalizedCost / numTrials;
        }
        
        /**
         * The number of trials used in the computation of the score.
         */
        public int getNumberOfTrials() {
            return numTrials;
        }
        
        /**
         * The variance of the normalized times used in the computation of the score.
         */
        public double getVariance() {
            // variance = (n*sum(X^2) - (sum(X)^2))/n^2
            int n = numTrials;
            double variance = (sumNormalizedCostSq * n -
                               sumNormalizedCost * sumNormalizedCost) / (n * n);
            return variance;
        }
        
        /**
         * The standard deviation of the normalized times used in the computation
         * of the score.
         */
        public double getStdDev() {
            return Math.sqrt(getVariance());
        }
        
        /**
         * The same as the score, but each trial is weighted by the absolute
         * time spent by the best trial of that operation.  This means that
         * operations that took longer will be weighted in this score more
         * heavily.
         */
        public double getWeightedMean() {
            return sumCost / sumMinimumCost;
        }
        
        /**
         * Returns the confidence interval of the normalized times with the given
         * significance level.
         */
        public double getConfidenceInterval(double sigLevel) {
            // sample mean +/- t(a/2,N-1)s/sqrt(N)
            int N = getNumberOfTrials();
            if (N < 2) return Double.POSITIVE_INFINITY;
            double s = getStdDev();
            return Distributions.uc_stDist(sigLevel/2, N-1) * s / Math.sqrt(N);
        }
        
        public void registerTrial(TrialInfo t) {
            registerTrials(Collections.singleton(t));
        }
        
        /**
         * Register new trials with this ConstraintInfo.
         */
        public void registerTrials(Collection newTrials) {
            for (Iterator i = newTrials.iterator(); i.hasNext(); ) {
                TrialInfo t = (TrialInfo) i.next();
                Order o = t.order;
                if (!o.obeysConstraint(c)) continue;
                TrialCollection tc = t.getCollection();
                long min = tc.getMinimum().cost;
                sumMinimumCost += min;
                double normalized = (double)t.cost / (double)min;
                sumNormalizedCost += normalized;
                sumNormalizedCostSq += normalized * normalized;
                trials.add(t);
                numTrials++;
            }
        }
        
        /**
         * Dump this constraint info to the screen.
         */
        public void dump() {
            System.out.println("Constraint: "+c);
            System.out.print("  Average="+format(getMean())+" (weighted="+format(getWeightedMean()));
            System.out.println(" stddev "+format(getStdDev())+" conf=+-"+format(getConfidenceInterval(.1)));
            System.out.println("   Based on "+numTrials+" trials:");
            for (Iterator i = trials.iterator(); i.hasNext(); ) {
                TrialInfo ti = (TrialInfo) i.next();
                System.out.println("    "+ti.toString());
            }
        }
        
        public Element toXMLElement() {
            Element dis = new Element("constraintInfo");
            Element constraint = c.toXMLElement();
            dis.setAttribute("sumCost", Double.toString(sumCost));
            dis.setAttribute("sumMinimumCost", Double.toString(sumMinimumCost));
            dis.setAttribute("sumNormalizedCost", Double.toString(sumNormalizedCost));
            dis.setAttribute("sumNormalizedCostSq", Double.toString(sumNormalizedCostSq));
            dis.setAttribute("numTrials", Integer.toString(numTrials));
            return dis;
        }
        
        public static ConstraintInfo fromXMLElement(Element e, XMLFactory f) {
            OrderConstraint c = null;
            for (Iterator i = e.getContent().iterator(); i.hasNext(); ) {
                Element e2 = (Element) i.next();
                Object o = f.fromXML(e2);
                if (o instanceof OrderConstraint) {
                    c = (OrderConstraint) o;
                    break;
                }
            }
            if (c == null) return null;
            ConstraintInfo ci = new ConstraintInfo(c);
            ci.sumCost = Double.parseDouble(e.getAttributeValue("sumCost", "0."));
            ci.sumMinimumCost = Double.parseDouble(e.getAttributeValue("sumMinimumCost", "0."));
            ci.sumNormalizedCost = Double.parseDouble(e.getAttributeValue("sumNormalizedCost", "0."));
            ci.sumNormalizedCostSq = Double.parseDouble(e.getAttributeValue("sumNormalizedCostSq", "0."));
            ci.numTrials = Integer.parseInt(e.getAttributeValue("numTrials", "0"));
            return ci;
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
    
    transient static NumberFormat nf;
    /**
     * Format a double in a nice way.
     * 
     * @param d  double
     * @return  string representation
     */
    public static String format(double d) {
        if (nf == null) {
            nf = NumberFormat.getNumberInstance();
            nf.setMinimumFractionDigits(3);
            nf.setMaximumFractionDigits(3);
        }
        return nf.format(d);
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
         * Collection that contains this trial.
         */
        TrialCollection collection;
        
        /**
         * Construct a new TrialInfo.
         * 
         * @param o  order
         * @param c  cost
         */
        public TrialInfo(Order o, long c, TrialCollection col) {
            this.order = o;
            this.cost = c;
            this.collection = col;
        }
        
        /**
         * @return  Returns the trial collection that this is a member of.
         */
        public TrialCollection getCollection() {
            return collection;
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
        
        public static TrialInfo fromXMLElement(Element e, Map nameToVar, TrialCollection col) {
            Order o = Order.parse(e.getAttributeValue("order"), nameToVar);
            long c = Long.parseLong(e.getAttributeValue("cost"));
            return new TrialInfo(o, c, col);
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
        public void addTrial(Order o, long cost, TrialCollection col) {
            addTrial(new TrialInfo(o, cost, col));
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
         * Calculates the standard deviation of a collection of trials.
         * 
         * @param trials  collection of trials
         * @return  variance
         */
        public static double getStdDev(Collection trials) {
            return Math.sqrt(getVariance(trials));
        }
        
        /**
         * @return  the standard deviation of the trials
         */
        public double getStdDev() {
            return getStdDev(trials.values());
        }
        
        /**
         * Calculates the variance of a collection of trials.
         * 
         * @param trials  collection of trials
         * @return  variance
         */
        public static double getVariance(Collection trials) {
            double sum = 0.;
            double sumOfSquares = 0.;
            int n = 0;
            for (Iterator i = trials.iterator(); i.hasNext(); ++n) {
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
         * @return  the variance of the trials
         */
        public double getVariance() {
            return getVariance(trials.values());
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
         * @return  the collection of trials
         */
        public Collection getTrials() {
            return trials.values();
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
                    TrialInfo ti = TrialInfo.fromXMLElement((Element) e2, nameToVar, tc);
                    tc.addTrial(ti);
                }
            }
            return tc;
        }
    }
    
    public static class ConstraintInfoCollection {
        
        Solver solver;
        
        /**
         * Map from orders to their info.
         */
        Map/*<OrderConstraint,ConstraintInfo>*/ infos;
        
        public ConstraintInfoCollection() {
            this.infos = new HashMap();
        }
        
        public ConstraintInfo getInfo(OrderConstraint c) {
            return (ConstraintInfo) infos.get(c);
        }
        
        public ConstraintInfo getOrCreateInfo(OrderConstraint c) {
            ConstraintInfo ci = (ConstraintInfo) infos.get(c);
            if (ci == null) infos.put(c, ci = new ConstraintInfo(c));
            return ci;
        }
        
        private void addTrials(TrialCollection tc, OrderTranslator trans) {
            for (Iterator i = tc.getTrials().iterator(); i.hasNext(); ) {
                TrialInfo ti = (TrialInfo) i.next();
                Order o = ti.order;
                if (trans != null) o = trans.translate(o);
                Collection ocs = o.getConstraints();
                for (Iterator j = ocs.iterator(); j.hasNext(); ) {
                    OrderConstraint oc = (OrderConstraint) j.next();
                    ConstraintInfo info = getOrCreateInfo(oc);
                    info.registerTrial(ti);
                }
            }
        }
        
        public void addTrials(TrialCollection tc) {
            InferenceRule ir = tc.getRule(solver);
            OrderTranslator varToAttrib = new VarToAttribTranslator(ir);
            addTrials(tc, varToAttrib);
            if (PER_RULE_CONSTRAINTS) {
                addTrials(tc, null);
            }
        }
        
    }
    
    public static void main(String[] args) {
        
        for (int i = 0; i < 20; ++i) {
            System.out.println("Recurrence A000670 ("+i+") = "+Distributions.recurrenceA000670(i));
        }
        List orders = generateAllOrders(Arrays.asList(args));
        System.out.println("Number of orders: "+orders.size());
        Iterator i = new OrderIterator(Arrays.asList(args));
        int k = 0;
        while (i.hasNext()) {
            Order o = (Order) i.next();
            System.out.println((++k)+": "+o);
            boolean b = orders.remove(o);
            Assert._assert(b);
            if (false) {
                Iterator j = new OrderIterator(Arrays.asList(args));
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
        Element constraintInfoCollection = new Element("constraintInfoCollection");
        for (Iterator i = constraintInfo.infos.entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry) i.next();
            OrderConstraint oc = (OrderConstraint) e.getKey();
            ConstraintInfo c = (ConstraintInfo) e.getValue();
            Element constraintInfo = c.toXMLElement();
            constraintInfoCollection.addContent(constraintInfo);
        }
        
        Element fbo = new Element("findBestOrder");
        fbo.addContent(constraintInfoCollection);
        
        return fbo;
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
