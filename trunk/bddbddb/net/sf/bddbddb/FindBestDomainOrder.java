// FindBestDomainOrder.java, created Aug 21, 2004 1:17:30 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.io.File;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.net.URL;
import java.text.NumberFormat;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Stack;

import jwutil.collections.GenericMultiMap;
import jwutil.collections.MultiMap;
import jwutil.math.Distributions;
import jwutil.util.Assert;
import net.sf.bddbddb.order.AttribToDomainMap;
import net.sf.bddbddb.order.AttribToDomainTranslator;
import net.sf.bddbddb.order.FilterTranslator;
import net.sf.bddbddb.order.MyId3;
import net.sf.bddbddb.order.Order;
import net.sf.bddbddb.order.OrderConstraint;
import net.sf.bddbddb.order.OrderConstraintSet;
import net.sf.bddbddb.order.OrderIterator;
import net.sf.bddbddb.order.OrderTranslator;
import net.sf.bddbddb.order.VarToAttribMap;
import net.sf.bddbddb.order.VarToAttribTranslator;
import net.sf.bddbddb.order.WekaInterface;
import net.sf.bddbddb.order.WekaInterface.OrderAttribute;
import net.sf.bddbddb.order.WekaInterface.OrderInstance;

import org.jdom.Document;
import org.jdom.Element;
import org.jdom.input.SAXBuilder;

import weka.classifiers.Classifier;
import weka.core.FastVector;
import weka.core.Instance;
import weka.core.Instances;
import weka.filters.Filter;
import weka.filters.unsupervised.attribute.Discretize;
import weka.filters.unsupervised.attribute.PKIDiscretize;

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
    
    /**
     * Whether we should keep track of per-rule constraints, in addition to global
     * constraints.
     */
    public static boolean PER_RULE_CONSTRAINTS = true;
    
    /**
     * Info collection for each of the constraints.
     */
    ConstraintInfoCollection constraintInfo;
    
    /**
     * Construct a new empty FindBestDomainOrder object.
     */
    public FindBestDomainOrder(Solver s) {
        constraintInfo = new ConstraintInfoCollection(s);
        allTrials = new LinkedList();
        solver = s;
    }
    
    /**
     * Construct a new FindBestDomainOrder object with the given info.
     */
    FindBestDomainOrder(ConstraintInfoCollection c) {
        constraintInfo = c;
        allTrials = new LinkedList();
        solver = c.solver;
    }
    
    /**
     * Load and incorporate trials from the given XML file.
     * 
     * @param filename  filename
     */
    void loadTrials(String filename) {
        out.println("Trials filename="+filename);
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
                    if (TRACE > 2) {
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
    
    /**
     * Incorporate all of the trials in allTrials.
     */
    void incorporateTrials() {
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection tc = (TrialCollection) i.next();
            constraintInfo.addTrials(tc);
        }
    }
    
   
    void incorporateTrial(TrialCollection c) {
        constraintInfo.addTrials(c);

        if (TRACE > 2)
            dump();
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
     * Starts a new trial collection and returns it.
     * 
     * @param id  name of trial collection
     * @param timeStamp  time of trial collection
     * @return  new trial collection
     */
    public TrialCollection getNewTrialCollection(String id, long timeStamp) {
        TrialCollection c = new TrialCollection(id, timeStamp);
        allTrials.add(c);
        return c;
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
            if (numTrials == 0) return 0.;
            return sumNormalizedCost / numTrials;
        }
        
        /**
         * The number of trials used in the computation of the score.
         */
        public int getNumberOfTrials() {
            return numTrials;
        }
        
        public static double getVariance(Collection cis) {
            double sum = 0.;
            double sumOfSquares = 0.;
            int n = 0;
            for (Iterator i = cis.iterator(); i.hasNext(); ) {
                ConstraintInfo ci = (ConstraintInfo) i.next();
                sum += ci.sumNormalizedCost;
                sumOfSquares += ci.sumNormalizedCostSq;
                n += ci.numTrials;
            }
            // variance = (n*sum(X^2) - (sum(X)^2))/n^2
            double variance = (sumOfSquares * n - sum * sum) / (n * n);
            return variance;
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
            if (sumMinimumCost == 0.) return 0.;
            return sumCost / sumMinimumCost;
        }
        
        public double getMinimumCost() {
            return sumMinimumCost;
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
            if (newTrials.isEmpty()) return;
            TrialCollection tc = ((TrialInfo)newTrials.iterator().next()).getCollection();
            long min = tc.getMinimum().cost + 1;
            sumMinimumCost += min;
            for (Iterator i = newTrials.iterator(); i.hasNext(); ) {
                TrialInfo t = (TrialInfo) i.next();
                Order o = t.order;
                //if (!o.obeysConstraint(c)) continue;
                sumCost += t.cost+1;
                double normalized = (double)(t.cost+1) / (double)min;
                sumNormalizedCost += normalized;
                sumNormalizedCostSq += normalized * normalized;
                trials.add(t);
                numTrials++;
            }
        }
        
        public int compareTo(Object o) {
            return compareTo((ConstraintInfo) o);
        }
        
        public int compareTo(ConstraintInfo that) {
            if (this == that) return 0;
            int result = signum(that.getWeightedMean() - this.getWeightedMean());
            if (result == 0) {
                result = (int) signum(this.getVariance() - that.getVariance());
                if (result == 0) {
                    result = this.c.compareTo(that.c);
                }
            }
            return result;
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
        
        public Element toXMLElement(Solver solver) {
            Element dis = new Element("constraintInfo");
            InferenceRule ir = null;
            if (c.isVariableConstraint()) ir = solver.getRuleThatContains((Variable) c.getFirst());
            Element constraint = c.toXMLElement(ir);
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
     * Calculated information about an order.  This consists of a score
     * and an estimated information gain.
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
         * A measure of how good this order is.
         */
        double score;
        
        /**
         * A measure of the expected information gain from running this order.
         */
        double infoGain;
        
        /**
         * Construct a new OrderInfo.
         * 
         * @param o  order
         * @param s  score
         * @param c  info gain
         */
        public OrderInfo(Order o, double s, double c) {
            this.order = o;
            this.score = s;
            this.infoGain = c;
        }
        
        /**
         * Construct a new OrderInfo that is a clone of another.
         * 
         * @param that  other OrderInfo to clone from
         */
        public OrderInfo(OrderInfo that) {
            this.order = that.order;
            this.score = that.score;
            this.infoGain = that.infoGain;
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return order+": score "+format(score)+" info gain "+format(infoGain);
        }

        /* (non-Javadoc)
         * @see java.lang.Comparable#compareTo(java.lang.Object)
         */
        public int compareTo(Object arg0) {
            return compareTo((OrderInfo) arg0);
        }
        /**
         * Comparison operator for OrderInfo objects.  Score is most important, followed
         * by info gain.  If both are equal, we compare the order lexigraphically.
         * 
         * @param that  OrderInfo to compare to
         * @return  -1, 0, or 1 if this OrderInfo is less than, equal to, or greater than the other
         */
        public int compareTo(OrderInfo that) {
            if (this == that) return 0;
            int result = signum(that.score - this.score);
            if (result == 0) {
                result = (int) signum(this.infoGain - that.infoGain);
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
            dis.setAttribute("infoGain", Double.toString(infoGain));
            return dis;
        }
        
        public static OrderInfo fromXMLElement(Element e, Map nameToVar) {
            Order o = Order.parse(e.getAttributeValue("order"), nameToVar);
            double s = Double.parseDouble(e.getAttributeValue("score"));
            double c = Double.parseDouble(e.getAttributeValue("infoGain"));
            return new OrderInfo(o, s, c);
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
        /*
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
        ArrayList/*<OrderInfo>*//* beforeConstraints = new ArrayList(vars.size()-1);
        ArrayList/*<OrderInfo>*//* afterConstraints = new ArrayList(vars.size()-1);
        while (it.hasNext()) {
            Object cadr = it.next();
            OrderConstraint before = OrderConstraint.makePrecedenceConstraint(car, cadr);
            ConstraintInfo before_i = constraints.getInfo(before);
            beforeConstraints.add(before_i);
            OrderConstraint after = OrderConstraint.makePrecedenceConstraint(cadr, car);
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
        */
        return null;
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
            //nf.setMinimumFractionDigits(3);
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
    
    
    public static class TrialPrediction {
        double [] predictions;
        public static int VARIABLE = 0;
        public static int ATTRIBUTE = 1;
        public static int DOMAIN = 2;
        
        public TrialPrediction(double varPredict, double attrPredict, double domPredict) {
            predictions = new double[3];
            predictions[VARIABLE] = varPredict;
            predictions[ATTRIBUTE] = attrPredict;
            predictions[DOMAIN] = domPredict;
        }
        
        public double getVarPrediction(){ return predictions[VARIABLE]; }
        public double getAttrPrediction(){ return predictions[ATTRIBUTE]; }
        public double getDomPrediction(){ return predictions[DOMAIN]; }
    }

    public static class TrialGuess {
        public Order order;

        public TrialPrediction prediction;

        public TrialGuess(Order o, TrialPrediction p) {
            order = o;
            prediction = p;
        }

        public Order getOrder() {
            return order;
        }

        public TrialPrediction getPrediction() {
            return prediction;
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
         * Collection that contains this trial.
         */
        TrialCollection collection;
        
        /*
         * The predicted results for this trial.
         */
        TrialPrediction pred;
        /**
         * Construct a new TrialInfo.
         * 
         * @param o  order
         * @param p predict value for this trial
         * @param c  cost
         */
        public TrialInfo(Order o, TrialPrediction p, long c, TrialCollection col) {
            this.order = o;
            this.pred = p;
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
            dis.setAttribute("varPredict", Double.toString(pred.getVarPrediction()));
            dis.setAttribute("attrPredict", Double.toString(pred.getAttrPrediction()));
            dis.setAttribute("domPredict", Double.toString(pred.getDomPrediction()));
            return dis;
        }
        
        public static TrialInfo fromXMLElement(Element e, Map nameToVar, TrialCollection col) {
            Order o = Order.parse(e.getAttributeValue("order"), nameToVar);
            long c = Long.parseLong(e.getAttributeValue("cost"));
            
            double vPredict = e.getAttributeValue("varPredict") == null ? Double.MAX_VALUE  : Double.parseDouble(e.getAttributeValue("varPredict"));
            double aPredict = e.getAttributeValue("attrPredict") == null ? Double.MAX_VALUE : Double.parseDouble(e.getAttributeValue("attrPredict"));
            double dPredict = e.getAttributeValue("domPredict") == null ? Double.MAX_VALUE  : Double.parseDouble(e.getAttributeValue("domPredict"));
            
            return new TrialInfo(o, new TrialPrediction(vPredict,aPredict,dPredict), c, col);
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
         * Best trial so far.
         */
        TrialInfo best;
        
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
            if (TRACE > 2) out.println(this+": Adding trial "+i);
            trials.put(i.order, i);
            if (best == null || best.cost > i.cost) {
                best = i;
            }
            sorted = null;
        }
        
        /**
         * Add the information about a trial to this collection.
         * 
         * @param o  order
         * @param p predicted value for this trial
         * @param cost  cost of operation
         */
        public void addTrial(Order o, TrialPrediction p, long cost) {
            addTrial(new TrialInfo(o, p, cost, this));
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
            InferenceRule rule = solver.getRule(ruleNum);
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
        
        public ConstraintInfoCollection(Solver s) {
            this.solver = s;
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
            MultiMap c2Trials = new GenericMultiMap();
            
           
            for (Iterator i = tc.getTrials().iterator(); i.hasNext(); ) {
                TrialInfo ti = (TrialInfo) i.next();
                Order o = ti.order;
                if (ti.cost >= BDDInferenceRule.LONG_TIME)
                    ((BDDSolver)solver).fbo.neverTryAgain(tc.getRule(solver), o);
                if (trans != null) o = trans.translate(o);
                Collection ocs = o.getConstraints();
                for (Iterator j = ocs.iterator(); j.hasNext(); ) {
                    OrderConstraint oc = (OrderConstraint) j.next();
                    c2Trials.add(oc, ti);
                }
                
              
            }
    
            
            for (Iterator i = c2Trials.keySet().iterator(); i.hasNext(); ) {
                OrderConstraint oc = (OrderConstraint) i.next();
                ConstraintInfo info = getOrCreateInfo(oc);
                info.registerTrials(c2Trials.getValues(oc));
            }
        }
        
        public void addTrials(TrialCollection tc) {
            InferenceRule ir = tc.getRule(solver);
            OrderTranslator varToAttrib = new VarToAttribTranslator(ir);
            addTrials(tc, varToAttrib);
            if (PER_RULE_CONSTRAINTS) {
                addTrials(tc, null);
            }
            if (TRACE > 2) {
                out.println("Added trial collection: "+tc);
            }
        }
        
        public OrderInfo predict(Order o, OrderTranslator trans) {
            if (TRACE > 2) out.println("Predicting order "+o);
            if (trans != null) o = trans.translate(o);
            if (TRACE > 2) out.println("Translated into order "+o);
            double score = 0.;
            int numTrialCollections = 0, numTrials = 0;
            Collection cinfos = new LinkedList();
            for (Iterator i = o.getConstraints().iterator(); i.hasNext(); ) {
                OrderConstraint c = (OrderConstraint) i.next();
                ConstraintInfo ci = getInfo(c);
                if (ci == null || ci.getNumberOfTrials() == 0) continue;
                cinfos.add(ci);
                score += ci.getWeightedMean();
                numTrialCollections++;
                numTrials += ci.getNumberOfTrials();
            }
            if (numTrialCollections == 0)
                score = 0.;
            else
                score = score / numTrialCollections;
            double infoGain = ConstraintInfo.getVariance(cinfos) / numTrials;
            if (TRACE > 2) out.println("Prediction for "+o+": score "+format(score)+" infogain "+format(infoGain));
            return new OrderInfo(o, score, infoGain);
        }
        
    }
    
    public OrderInfo predict(Order o, OrderTranslator trans) {
        return constraintInfo.predict(o, trans);
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
            Element constraintInfo = c.toXMLElement(solver);
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

    /**
     * @param allVars
     * @param t
     * @return
     */
    public boolean hasOrdersToTry(List allVars, OrderTranslator t) {
        // TODO: improve this code.
        return true;
    }

    /**
     * @param tc
     * @param allVars
     * @param t
     * @return
     */
    public Order tryNewGoodOrder(TrialCollection tc, List allVars, OrderTranslator t) {
        // TODO: improve this code.
        OrderInfo best = null;
        Order bestOrder = null;
        OrderIterator i = new OrderIterator(allVars);
        while (i.hasNext()) {
            Order o = i.nextOrder();
            if (tc.contains(o)) continue;
            OrderInfo oi = predict(o, t);
            if (PER_RULE_CONSTRAINTS) {
                OrderInfo oi2 = predict(o, null);
                oi.score = (oi.score + oi2.score) / 2;
                oi.infoGain = (oi.infoGain + oi2.infoGain) / 2;
            }
            if (best == null || best.compareTo(oi) < 0) {
                best = oi;
                bestOrder = o;
            }
        }
        if (TRACE > 1) out.println("Best = "+best+" order = "+bestOrder);
        return bestOrder;
    }
    
    public static class TrialInstance extends OrderInstance implements Comparable {
        
        public static TrialInstance construct(TrialInfo ti, Order o, double cost, Instances dataSet) {
            return construct(ti, o, cost, dataSet, 1);
        }
        
        public static TrialInstance construct(TrialInfo ti, Order o, double cost, Instances dataSet, double weight) {
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
                    d[oa.index()] = WekaInterface.getType(oc);
                } else {
                    //System.out.println("Warning: cannot find constraint "+oc+" order "+ti.order+" in dataset "+dataSet.relationName());
                    return null;
                }
            }
            d[d.length-1] = cost;
            return new TrialInstance(weight, d, o, ti);
        }
        
        TrialInfo ti;
        
        protected TrialInstance(double weight, double[] d, Order o, TrialInfo ti) { 
            super(weight, d, o);
            this.ti = ti;
        }
        
        protected TrialInstance(TrialInstance that) {
            super(that);
            this.ti = that.ti;
        }
        
        public TrialInfo getTrialInfo(){ return ti; }
        
        public double getCost() {
            return value(numAttributes()-1);
        }
        
        public Object copy() {
            return new TrialInstance(this);
        }

        public int compareTo(Object arg0) {
            TrialInstance that = (TrialInstance) arg0;
            return compare(this.getCost(), that.getCost());
        }
        
        public boolean isMaxTime() {
            return ti.cost >= BDDInferenceRule.LONG_TIME;
        }
        
    }
    
    // JDK1.4 only.
    public static final int compare(double d1, double d2) {
        if (d1 < d2)
            return -1;       // Neither val is NaN, thisVal is smaller
        if (d1 > d2)
            return 1;        // Neither val is NaN, thisVal is larger

        long thisBits = Double.doubleToLongBits(d1);
        long anotherBits = Double.doubleToLongBits(d2);

        return (thisBits == anotherBits ?  0 : // Values are equal
                (thisBits < anotherBits ? -1 : // (-0.0, 0.0) or (!NaN, NaN)
                 1));                          // (0.0, -0.0) or (NaN, !NaN)
    }
    
    public static class TrialInstances extends Instances {

        /**
         * @param name
         * @param attInfo
         * @param capacity
         */
        public TrialInstances(String name, FastVector attInfo, int capacity) {
            super(name, attInfo, capacity);
        }
        
        public void threshold(double thres) {
            threshold(thres, this.classIndex());
        }
        
        public void threshold(double thres, int index) {
            FastVector clusterValues = new FastVector(2);
            clusterValues.addElement("<"+format(thres));
            clusterValues.addElement(">"+format(thres));
            weka.core.Attribute a = new weka.core.Attribute("costThres"+format(thres), clusterValues);
            m_Attributes.setElementAt(a, index);
            setIndex(a, index);
            Enumeration f = m_Instances.elements();
            while (f.hasMoreElements()) {
                Instance old_i = (Instance) f.nextElement();
                double oldVal = old_i.value(index);
                double val = oldVal < thres ? 0 : 1;
                old_i.setValue(index, val);
            }
        }
        
        public double[] discretize() {
            int numBins = (int) Math.sqrt(numInstances());
            return discretize(new PKIDiscretize(), numBins, this.classIndex());
        }
        
        public double[] discretize(Discretize d, int numBins, int index) {
            try {
                int classIndex = this.classIndex();
                setClassIndex(-1); // clear class instance for discretization.
                d.setAttributeIndices(Integer.toString(index+1)); // RANGE IS 1-BASED!!!
                d.setInputFormat(this); // NOTE: this must be LAST because it calls setUpper
                Instances newInstances;
                newInstances = Filter.useFilter(this, d);
                if (d.getFindNumBins()) numBins = d.getBins();
                double[] result = d.getCutPoints(index);
                weka.core.Attribute a = makeBucketAttribute(numBins);
                m_Attributes.setElementAt(a, index);
                setIndex(a, index);
                Enumeration e = newInstances.enumerateInstances();
                Enumeration f = m_Instances.elements();
                while (e.hasMoreElements()) {
                    Instance new_i = (Instance) e.nextElement();
                    Instance old_i = (Instance) f.nextElement();
                    double val = new_i.value(index);
                    old_i.setValue(index, val);
                }
                setClassIndex(classIndex); // reset class index.
                Assert._assert(!f.hasMoreElements());
                return result;
            } catch (Exception x) {
                x.printStackTrace();
                return null;
            }
        }
        
        static void setIndex(weka.core.Attribute a, int i) {
            try {
                Class c = Class.forName("weka.core.Attribute");
                Field f = c.getDeclaredField("m_Index");
                f.setAccessible(true);
                f.setInt(a, i);
            } catch (Exception x) {
                Assert.UNREACHABLE("weka sucks: "+x);
            }
        }
        
    }
    
    static weka.core.Attribute makeBucketAttribute(int numClusters) {
        FastVector clusterValues = new FastVector(numClusters);
        for(int i = 0; i < numClusters; ++i)
            clusterValues.addElement(Integer.toString(i));
        return new weka.core.Attribute("costBucket", clusterValues);
    }
    
    void addToInstances(Instances data, TrialCollection tc, OrderTranslator t) {
        if (tc.size() == 0) return;
        double best = (double) tc.getMinimum().cost+1;
        for (Iterator j = tc.trials.values().iterator(); j.hasNext(); ) {
            TrialInfo ti = (TrialInfo) j.next();
            double score = (double) (ti.cost+1) / best;
            Order o = t == null ? ti.order : t.translate(ti.order);
            if (o.numberOfElements() <= 1) continue;
            TrialInstance tinst = TrialInstance.construct(ti, o, score, data); 
            if (tinst != null) data.add(tinst);
        }
    }
    
    TrialInstances buildVarInstances(InferenceRule ir, List allVars) {
        if (allVars.size() <= 1) return null;
        FastVector attributes = new FastVector();
        WekaInterface.addAllPairs(attributes, allVars);
        attributes.addElement(new weka.core.Attribute("score"));
        int capacity = 30;
        OrderTranslator filter = new FilterTranslator(allVars);
        TrialInstances data = new TrialInstances("Var Ordering Constraints", attributes, capacity);
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection tc2 = (TrialCollection) i.next();
            InferenceRule ir2 = tc2.getRule(solver);
            if (ir != ir2) continue;
            addToInstances(data, tc2, filter);
        }
        data.setClassIndex(data.numAttributes()-1);
        return data;
    }
    
    TrialInstances buildAttribInstances(InferenceRule ir, List allVars) {
        List allAttribs = VarToAttribMap.convert(allVars, ir);
        if (TRACE > 1) out.println("Attribs: "+allAttribs);
        if (allAttribs.size() <= 1) return null;
        FastVector attributes = new FastVector();
        WekaInterface.addAllPairs(attributes, allAttribs);
        attributes.addElement(new weka.core.Attribute("score"));
        int capacity = 30;
        TrialInstances data = new TrialInstances("Attribute Ordering Constraints", attributes, capacity);
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection tc2 = (TrialCollection) i.next();
            InferenceRule ir2 = tc2.getRule(solver);
            OrderTranslator t = new VarToAttribTranslator(ir2);
            t = new OrderTranslator.Compose(t, new FilterTranslator(allAttribs));
            addToInstances(data, tc2, t);
        }
        data.setClassIndex(data.numAttributes()-1);
        return data;
    }
    
    TrialInstances buildDomainInstances(InferenceRule ir, List allVars) {
        List allDomains = AttribToDomainMap.convert(VarToAttribMap.convert(allVars, ir));
        if (TRACE > 1) out.println("Domains: "+allDomains);
        if (allDomains.size() <= 1) return null;
        FastVector attributes = new FastVector();
        WekaInterface.addAllPairs(attributes, allDomains);
        attributes.addElement(new weka.core.Attribute("score"));
        int capacity = 30;
        TrialInstances data = new TrialInstances("Domain Ordering Constraints", attributes, capacity);
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection tc2 = (TrialCollection) i.next();
            InferenceRule ir2 = tc2.getRule(solver);
            OrderTranslator t = new VarToAttribTranslator(ir2);
            t = new OrderTranslator.Compose(t, AttribToDomainTranslator.INSTANCE);
            t = new OrderTranslator.Compose(t, new FilterTranslator(allDomains));
            addToInstances(data, tc2, t);
        }
        data.setClassIndex(data.numAttributes()-1);
        return data;
    }
    
    public Classifier buildClassifier(String cClassName, Instances data) {
        // Build the classifier.
        Classifier classifier = null;
        try {
            long time = System.currentTimeMillis();
            classifier = (Classifier) Class.forName(cClassName).newInstance();
            classifier.buildClassifier(data);
            if (TRACE > 1) System.out.println("Classifier "+cClassName+" took "+(System.currentTimeMillis()-time)+" ms to build.");
            if (TRACE > 2) System.out.println(classifier);
        } catch (Exception x) {
            out.println(cClassName+": "+x.getLocalizedMessage());
            return null;
        }
        return classifier;
    }
    
    public final static int WEIGHT_WINDOW_SIZE = Integer.MAX_VALUE;
    public final static double DECAY_FACTOR = -.1;

    public double computeWeight(int type, TrialInstances instances){
        int numTrials = 0;
        int losses = 0;
        double weight = 1;
        for(int i = instances.numInstances() - 1; i >= 0 && numTrials < WEIGHT_WINDOW_SIZE;--i){
           TrialInstance instance = (TrialInstance) instances.instance(i);
           double trueCost = instance.getCost();
           double predCost = instance.getTrialInfo().pred.predictions[type];
           if(predCost < trueCost){
               losses += Math.exp(DECAY_FACTOR * numTrials);
           }
           ++numTrials;
        }
        if (numTrials != 0) {
            weight = 1 - losses / (double) numTrials;
        }
        return weight;
    }
    public void adjustWeights(TrialInstances vData, TrialInstances aData, TrialInstances dData){
        varClassWeight = computeWeight(TrialPrediction.VARIABLE, vData);
        attrClassWeight = computeWeight(TrialPrediction.ATTRIBUTE, aData);
        domClassWeight = computeWeight(TrialPrediction.DOMAIN, dData);
    
    }
    public static int NUM_CV_FOLDS = 10;

    public double genAccuracy(String cClassName, Instances data0) {
        Instances data = new Instances(data0);
        //should stratify
        data.randomize(new Random(System.currentTimeMillis()));
        Assert._assert(data.classAttribute() != null);
        if (data.numInstances() < NUM_CV_FOLDS)
            return Double.NaN; //more folds than elements
        if (data.numInstances() == 0)
            return Double.NaN; //no instances
        double[] estimates = new double[NUM_CV_FOLDS];
        for (int i = 0; i < NUM_CV_FOLDS; ++i) {
            Instances trainData = data.trainCV(NUM_CV_FOLDS, i);
            Assert._assert(trainData.classAttribute() != null);
            Assert._assert(trainData.numInstances() != 0, "Cannot train classifier on 0 instances.");

            Instances testData = data.testCV(NUM_CV_FOLDS, i);
            Assert._assert(testData.classAttribute() != null);
            Assert._assert(testData.numInstances() != 0, "Cannot test classifier on 0 instances.");

            int temp = TRACE;
            TRACE = 0;
            Classifier classifier = buildClassifier(cClassName, trainData);
            TRACE = temp;
            int count = testData.numInstances();
            for (Enumeration e = testData.enumerateInstances(); e.hasMoreElements();) {
                Instance instance = (Instance) e.nextElement();
                Assert._assert(instance.classAttribute() != null && instance.classAttribute() == trainData.classAttribute());
                Assert._assert(instance != null);
                try {
                    double testClass = classifier.classifyInstance(instance);
                    if (testClass != instance.classValue())
                        --count;
                } catch (Exception ex) {
                    out.println("Exception while classifying: " + instance + "\n" + ex);
                }
            }
            estimates[i] = count / (double) testData.numInstances();
        }
        double average = 0;
        for (int i = 0; i < NUM_CV_FOLDS; ++i)
            average += estimates[i];

        return average / NUM_CV_FOLDS;
    }
    public static boolean DISCRETIZE1 = true;
    public static boolean DISCRETIZE2 = true;
    public static boolean DISCRETIZE3 = true;
    public static String CLASSIFIER1 = "net.sf.bddbddb.order.MyId3";
    public static String CLASSIFIER2 = "net.sf.bddbddb.order.MyId3";
    public static String CLASSIFIER3 = "net.sf.bddbddb.order.MyId3";
    
    public void neverTryAgain(InferenceRule ir, Order o) {
        if (TRACE > 2) out.println("For rule"+ir.id+", never trying order "+o+" again.");
        neverAgain.add(ir, o);
    }
    
    MultiMap neverAgain = new GenericMultiMap();
    

    public double varClassWeight = 1;
    public double attrClassWeight = 1;
    public double domClassWeight = 1;
    public static int DOMAIN_THRESHOLD = 1000;
    public TrialGuess tryNewGoodOrder2(TrialCollection tc, List allVars, InferenceRule ir) {
        
        // TODO: improve this code.
        TrialInstances vData, aData, dData;
        vData = buildVarInstances(ir, allVars);
        aData = buildAttribInstances(ir, allVars);
        dData = buildDomainInstances(ir, allVars);
        
        adjustWeights(vData,aData,dData);
        double [] vBuckets = null, aBuckets = null, dBuckets = {DOMAIN_THRESHOLD, Double.MAX_VALUE};
        if (DISCRETIZE1) vBuckets = vData.discretize();
        if (DISCRETIZE2) aBuckets = aData.discretize();
        if (DISCRETIZE3) dData.threshold(1000);
        
        double vGenErr, aGenErr, dGenErr;
        vGenErr = genAccuracy(CLASSIFIER1, vData);
        aGenErr = genAccuracy(CLASSIFIER2, aData);
        dGenErr = genAccuracy(CLASSIFIER3, dData);
        
        if (TRACE > 1) {
            out.println(" Var data points: "+vData.numInstances());
            out.println(" Var Classifier Accuracy: " + vGenErr);
            out.println(" Var Classifier Weight: " + varClassWeight);
            //out.println(" Var data points: "+vData);
            out.println(" Attrib data points: "+aData.numInstances());
            out.println(" Attrib Classifier Accuracy: " + aGenErr);
            out.println(" Attrib Classifier Weight: " + attrClassWeight);
            out.println(" Domain data points: "+dData.numInstances());
            out.println(" Domain Classifier Accuracy: " + dGenErr);
            out.println(" Domain Classifier Weight: " + domClassweight);
            //out.println(" Domain data points: "+dData);
        
        }
        
        Classifier vClassifier = null, aClassifier = null, dClassifier = null;
        if (vData.numInstances() > 0)
            vClassifier = buildClassifier(CLASSIFIER1, vData);
        if (aData.numInstances() > 0)
            aClassifier = buildClassifier(CLASSIFIER2, aData);
        if (dData.numInstances() > 0)
            dClassifier = buildClassifier(CLASSIFIER3, dData);
        
        if (TRACE > 2) {
            out.println("Var classifier: "+vClassifier);
            out.println("Attrib classifier: "+aClassifier);
            out.println("Domain classifier: "+dClassifier);
        }
        
        // Iterate through all orders, classify them, and find the best one.
        OrderTranslator v2a = new VarToAttribTranslator(ir);
        OrderTranslator a2d = AttribToDomainTranslator.INSTANCE;
        OrderIterator i = new OrderIterator(allVars);
        Order best = null; double bestScore = Double.MAX_VALUE;
        TrialPrediction prediction = null;
        Collection never = neverAgain.getValues(ir);
        while (i.hasNext()) {
            Order o_v = i.nextOrder();
            if (tc != null && tc.contains(o_v)) continue;
            if (never != null && never.contains(o_v)) continue;
            
            double vScore = -1., aScore = -1., dScore = -1.;
            
            if (vClassifier != null) {
                OrderInstance vInst = OrderInstance.construct(o_v, vData);
                try {
                    vScore = vClassifier.classifyInstance(vInst);
                } catch (Exception x) {
                    out.println("Exception while predicting "+vInst+" "+o_v+":\n"+x);
                }
                if (TRACE > 2) out.println("Order "+vInst.getOrder()+" score = "+vScore);
            }
            
            Order o_a = v2a.translate(o_v);
            if (aClassifier != null) {
                OrderInstance aInst = OrderInstance.construct(o_a, aData);
                try {
                    aScore = aClassifier.classifyInstance(aInst);
                } catch (Exception x) {
                    out.println("Exception while predicting "+aInst+" "+o_a+":\n"+x);
                }
                if (TRACE > 2) out.println("Order "+aInst.getOrder()+" score = "+aScore);
            }
            
            if (dClassifier != null) {
                Order o_d = a2d.translate(o_a);
                OrderInstance dInst = OrderInstance.construct(o_d, dData);
                try {
                    dScore = dClassifier.classifyInstance(dInst);
                } catch (Exception x) {
                    out.println("Exception while predicting "+dInst+" "+o_d+":\n"+x);
                }
                if (TRACE > 2) out.println("Order "+dInst.getOrder()+" score = "+dScore);
            }
            
            // Combine the scores in some fashion.
            double score = vScore  +  aScore  + dScore * 10;
            if (best == null || bestScore > score) {
                if (TRACE > 1) out.println("Better order "+o_v+" score = "+score+" (v="+vScore+",a="+aScore+",d="+dScore+")");
                best = o_v;
                bestScore = score;
                
                if (vBuckets != null && vScore != -1){
                    vScore = vScore == vBuckets.length ?  Double.MAX_VALUE : vBuckets[(int) vScore];
                }
                if (aBuckets != null && aScore != -1){
                    aScore = aScore == aBuckets.length ? Double.MAX_VALUE : aBuckets[(int) aScore];
                }
                if(dBuckets != null && dScore != -1){
                    dScore = dScore == dBuckets.length ? Double.MAX_VALUE : dBuckets[(int) dScore];
                }
                prediction = new TrialPrediction(vScore,aScore,dScore);
            }
        }
        if (TRACE > 1) out.println("Best = "+best+" score = "+bestScore);
        
        if (true) {
            MyId3 v = (MyId3) vClassifier;
            MyId3 a = (MyId3) aClassifier;
            MyId3 d = (MyId3) dClassifier;
            if (v != null) printGoodOrder(allVars, vData, v);
            List allAttribs = VarToAttribMap.convert(allVars, ir);
            if (a != null) printGoodOrder(allAttribs, aData, a);
        }
        return new TrialGuess(best, prediction);
    }
    
    void printGoodOrder(Collection allVars, Instances inst, MyId3 v) {
        Collection vBestAttribs = v.getAttribCombos(inst.numAttributes(), 0.);
        if (vBestAttribs != null) {
outer:
            for (Iterator ii = vBestAttribs.iterator(); ii.hasNext(); ) {
                double[] c = (double[]) ii.next();
                OrderConstraintSet ocs = new OrderConstraintSet();
                for (int iii = 0; iii < c.length; ++iii) {
                    if (Double.isNaN(c[iii])) continue;
                    int k = (int) c[iii];
                    OrderAttribute oa = (OrderAttribute) inst.attribute(iii);
                    out.println(oa);
                    OrderConstraint oc = oa.getConstraint(k);
                    out.println(oc);
                    boolean r = ocs.constrain(oc);
                    if (!r) {
                        if (TRACE > 1) out.println("Constraint "+oc+" conflicts with "+ocs);
                        continue outer;
                    }
                }
                Order o = ocs.generateOrder(allVars);
                out.println("Good order: "+o);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        String inputFilename = System.getProperty("datalog");
        if (args.length > 0) inputFilename = args[0];
        if (inputFilename == null) {
            return;
        }
        String solverName = System.getProperty("solver", "net.sf.bddbddb.BDDSolver");
        Solver s;
        s = (Solver) Class.forName(solverName).newInstance();
        s.load(inputFilename);
        
        FindBestDomainOrder dis = ((BDDSolver)s).fbo;
        //dis.loadTrials("trials.xml");
        //dis.dump();
        
        for (Iterator i = s.rules.iterator(); i.hasNext(); ) {
            InferenceRule ir = (InferenceRule) i.next();
            if (ir.necessaryVariables == null) continue;
            System.out.println("Computing for rule "+ir);
            
            List allVars = new LinkedList();
            allVars.addAll(ir.necessaryVariables);
            System.out.println("Variables = "+allVars);
            
            TrialGuess guess = dis.tryNewGoodOrder2(null, allVars, ir);
            Order order = guess.order;
            
            System.out.println("Resulting order: "+order);
        }
        
    }
}
