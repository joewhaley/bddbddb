// FindBestDomainOrder.java, created Aug 21, 2004 1:17:30 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.net.URL;
import java.text.NumberFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import jwutil.collections.FlattenedCollection;
import jwutil.collections.GenericMultiMap;
import jwutil.collections.MultiMap;
import jwutil.math.Distributions;
import jwutil.util.Assert;
import net.sf.bddbddb.order.AttribToDomainMap;
import net.sf.bddbddb.order.AttribToDomainTranslator;
import net.sf.bddbddb.order.ClassProbabilityEstimator;
import net.sf.bddbddb.order.FilterTranslator;
import net.sf.bddbddb.order.MapBasedTranslator;
import net.sf.bddbddb.order.MyDiscretize;
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
 *   Rule -> ConstraintInfo collection
 * TrialCollection -> ConstraintInfo collection
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
    public static PrintStream out_t = null;

    static final SimpleDateFormat dateFormat = new SimpleDateFormat("yyMMdd-HHmmss");

    /**
     * Link back to the solver.
     */
    BDDSolver solver;

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

    public static boolean DUMP_CLASSIFIER_INFO = false;

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
        if (s instanceof BDDSolver)
            solver = (BDDSolver) s;
    }

    /**
     * Construct a new FindBestDomainOrder object with the given info.
     */
    FindBestDomainOrder(ConstraintInfoCollection c) {
        constraintInfo = c;
        allTrials = new LinkedList();
        if (c.solver instanceof BDDSolver)
            solver = (BDDSolver) c.solver;
    }

    /**
     * Load and incorporate trials from the given XML file.
     * 
     * @param filename  filename
     */
    void loadTrials(String filename) {
        out.println("Trials filename=" + filename);
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
                    out.println("Loaded " + list.size() + " trial collections from file.");
                    if (TRACE > 2) {
                        for (Iterator i = list.iterator(); i.hasNext();) {
                            out.println("Loaded from file: " + i.next());
                        }
                    }
                }
                allTrials.addAll(list);
            } catch (Exception e) {
                System.err.println("Error occurred loading " + filename + ": " + e);
                e.printStackTrace();
            }
        }
        incorporateTrials();
    }

    /**
     * Incorporate all of the trials in allTrials.
     */
    void incorporateTrials() {
        for (Iterator i = allTrials.iterator(); i.hasNext();) {
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
        SortedSet set = new TreeSet(new Comparator() {
            public int compare(Object o1, Object o2) {
                ConstraintInfo info1 = (ConstraintInfo) ((Map.Entry) o1).getValue();
                ConstraintInfo info2 = (ConstraintInfo) ((Map.Entry) o2).getValue();
                return info1.compareTo(info2);
            }
        });
        set.addAll(constraintInfo.infos.entrySet());
        for (Iterator i = set.iterator(); i.hasNext();) {
            Map.Entry e = (Map.Entry) i.next();
            OrderConstraint ir = (OrderConstraint) e.getKey();
            System.out.println("Order feature: " + ir);
            ConstraintInfo info = (ConstraintInfo) e.getValue();
            info.dump();
        }
    }

    public int getNumberOfTrials() {
        int sum = 0;
        for (Iterator i = allTrials.iterator(); i.hasNext();) {
            TrialCollection tc = (TrialCollection) i.next();
            sum += tc.size();
        }
        return sum;
    }
    
    /**
     * Starts a new trial collection and returns it.
     * 
     * @param id  name of trial collection
     * @param timeStamp  time of trial collection
     * @return new trial collection
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
    public static class ConstraintInfo implements Comparable {

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

        /** * The rest of the fields are computed based on the trials. ** */

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
            return c + ": score " + format(getMean()) + " +- " + format(getConfidenceInterval(.1));
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
            for (Iterator i = cis.iterator(); i.hasNext();) {
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
         * time spent by the best trial of that operation. This means that
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
            return Distributions.uc_stDist(sigLevel / 2, N - 1) * s / Math.sqrt(N);
        }

        public void registerTrial(TrialInfo t) {
            registerTrials(Collections.singleton(t));
        }

        /**
         * Register new trials with this ConstraintInfo.
         */
        public void registerTrials(Collection newTrials) {
            if (newTrials.isEmpty()) return;
            TrialCollection tc = ((TrialInfo) newTrials.iterator().next()).getCollection();
            long min = tc.getMinimum().cost + 1;
            sumMinimumCost += min;
            for (Iterator i = newTrials.iterator(); i.hasNext();) {
                TrialInfo t = (TrialInfo) i.next();
                Order o = t.order;
                //if (!o.obeysConstraint(c)) continue;
                sumCost += t.cost + 1;
                double normalized = (double) (t.cost + 1) / (double) min;
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
            System.out.println("Constraint: " + c);
            System.out.print("  Average=" + format(getMean()) + " (weighted=" + format(getWeightedMean()));
            System.out.println(" stddev " + format(getStdDev()) + " conf=+-" + format(getConfidenceInterval(.1)));
            System.out.println("   Based on " + numTrials + " trials:");
            for (Iterator i = trials.iterator(); i.hasNext();) {
                TrialInfo ti = (TrialInfo) i.next();
                System.out.println("    " + ti.toString());
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
            for (Iterator i = e.getContent().iterator(); i.hasNext();) {
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
            return order + ": score " + format(score) + " info gain " + format(infoGain);
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
         * @return XML element
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
    public static List/*<Order>*/ generateAllOrders(List vars) {
        if (vars.size() == 0) return null;
        LinkedList result = new LinkedList();
        if (vars.size() == 1) {
            result.add(new Order(vars));
            return result;
        }
        Object car = vars.get(0);
        List recurse = generateAllOrders(vars.subList(1, vars.size()));
        for (Iterator i = recurse.iterator(); i.hasNext();) {
            Order order = (Order) i.next();
            for (int j = 0; j <= order.size(); ++j) {
                Order myOrder = new Order(order);
                myOrder.add(j, car);
                result.add(myOrder);
            }
        }
        for (Iterator i = recurse.iterator(); i.hasNext();) {
            Order order = (Order) i.next();
            for (int j = 0; j < order.size(); ++j) {
                Order myOrder = new Order(order);
                Object o = myOrder.get(j);
                List c = new LinkedList();
                c.add(car);
                if (o instanceof Collection) {
                    c.addAll((Collection) o);
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
     * @return string representation
     */
    public static String format(double d) {
        if (nf == null) {
            nf = NumberFormat.getNumberInstance();
            //nf.setMinimumFractionDigits(3);
            nf.setMaximumFractionDigits(3);
        }
        if (d == Double.MAX_VALUE) return "max";
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
        
        double score;
        
        double[][] predictions;

        public static int VARIABLE = 0;

        public static int ATTRIBUTE = 1;

        public static int DOMAIN = 2;

        public static int LOW = 0;

        public static int HIGH = 1;
        public TrialPrediction(double score,
                double varLowerBound, double varUpperBound, double attrLowerBound,
                double attrUpperBound,  double domLowerBound, double domUpperBound) {
            this.score = score;
            predictions = new double[3][];
            predictions[VARIABLE] = new double[2];
            predictions[VARIABLE][LOW] = varLowerBound;
            predictions[VARIABLE][HIGH] = varUpperBound;
            predictions[ATTRIBUTE] = new double[2];
            predictions[ATTRIBUTE][LOW] = attrLowerBound;
            predictions[ATTRIBUTE][HIGH] = attrUpperBound;
            predictions[DOMAIN] = new double[2];
            predictions[DOMAIN][LOW] = domLowerBound;
            predictions[DOMAIN][HIGH] = domUpperBound;
        }
        public double getVarLowerBound(){ return predictions[VARIABLE][LOW]; }
        public double getVarUpperBound(){ return predictions[VARIABLE][HIGH]; }
        public double getAttrLowerBound(){ return predictions[ATTRIBUTE][LOW]; }
        public double getAttrUpperBound(){ return predictions[ATTRIBUTE][HIGH]; }
        public double getDomLowerBound(){ return predictions[DOMAIN][LOW]; }
        public double getDomUpperBound(){ return predictions[DOMAIN][HIGH]; }
        public String toString() {
            return "score="+format(score)+", var=("+format(predictions[VARIABLE][LOW])+".."+format(predictions[VARIABLE][HIGH])+"),"+
               "attr=("+format(predictions[ATTRIBUTE][LOW])+".."+format(predictions[ATTRIBUTE][HIGH])+"),"+
               "domain=("+format(predictions[DOMAIN][LOW])+".."+format(predictions[DOMAIN][HIGH])+")";
        }
        public double getScore() {
            return score;
        }
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

        public String toString() {
            return "Order: " + order.toString() + " prediction: " + prediction.toString();
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

        /**
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
         * @return Returns the trial collection that this is a member of.
         */
        public TrialCollection getCollection() {
            return collection;
        }

        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return order + ": cost " + cost;
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

        public boolean isMax() {
            return cost == BDDInferenceRule.LONG_TIME;
        }

        public static String PREDICTION_VAR1 = "LowerBound";

        public static String PREDICTION_VAR2 = "UpperBound";

        /**
         * Returns this TrialInfo as an XML element.
         * 
         * @return XML element
         */
        public Element toXMLElement() {
            Element dis = new Element("trialInfo");
            dis.setAttribute("order", order.toString());
            dis.setAttribute("cost", Long.toString(cost));
            dis.setAttribute("var" + PREDICTION_VAR1, Double.toString(pred.getVarLowerBound()));
            dis.setAttribute("var" + PREDICTION_VAR2, Double.toString(pred.getVarUpperBound()));
            dis.setAttribute("attr" + PREDICTION_VAR1, Double.toString(pred.getAttrLowerBound()));
            dis.setAttribute("attr" + PREDICTION_VAR2, Double.toString(pred.getAttrUpperBound()));
            dis.setAttribute("dom" + PREDICTION_VAR1, Double.toString(pred.getDomLowerBound()));
            dis.setAttribute("dom" + PREDICTION_VAR2, Double.toString(pred.getDomUpperBound()));
            return dis;
        }

        public static TrialInfo fromXMLElement(Element e, Map nameToVar, TrialCollection col) {
            Order o = Order.parse(e.getAttributeValue("order"), nameToVar);
            long c = Long.parseLong(e.getAttributeValue("cost"));

            String score1 = e.getAttributeValue("score");
            double score = score1 == null ? 0 : Double.parseDouble(score1);
            String var1 = e.getAttributeValue("var" + PREDICTION_VAR1);
            String var2 = e.getAttributeValue("var" + PREDICTION_VAR2);
            double vVar1 = var1 == null ? 0 : Double.parseDouble(var1);
            double vVar2 = var2 == null ? Double.MAX_VALUE : Double.parseDouble(var2);
            var1 = e.getAttributeValue("attr" + PREDICTION_VAR1);
            var2 = e.getAttributeValue("attr" + PREDICTION_VAR2);
            double aVar1 = var1 == null ? 0 : Double.parseDouble(var1);
            double aVar2 = var2 == null ? Double.MAX_VALUE : Double.parseDouble(var2);
            var1 = e.getAttributeValue("dom" + PREDICTION_VAR1);
            var2 = e.getAttributeValue("dom" + PREDICTION_VAR2);
            double dVar1 = var1 == null ? 0 : Double.parseDouble(var1);
            double dVar2 = var2 == null ? Double.MAX_VALUE : Double.parseDouble(var2);
            return new TrialInfo(o, new TrialPrediction(score, vVar1, vVar2, aVar1, aVar2, dVar1, dVar2), c, col);
        }
    }

    /**
     * A collection of trials on the same test. (The same BDD operation.)
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
         * Trial info sorted by cost. Updated automatically when necessary.
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
         * @return true if this collection contains it, false otherwise
         */
        public boolean contains(Order o) {
            return trials.containsKey(o);
        }

        /**
         * Calculates the standard deviation of a collection of trials.
         * 
         * @param trials  collection of trials
         * @return variance
         */
        public static double getStdDev(Collection trials) {
            return Math.sqrt(getVariance(trials));
        }

        /**
         * @return the standard deviation of the trials
         */
        public double getStdDev() {
            return getStdDev(trials.values());
        }

        /**
         * Calculates the variance of a collection of trials.
         * 
         * @param trials  collection of trials
         * @return variance
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
         * @return the variance of the trials
         */
        public double getVariance() {
            return getVariance(trials.values());
        }

        /**
         * @return the minimum cost trial
         */
        public TrialInfo getMinimum() {
            return best;
        }

        /**
         * @return the maximum cost trial
         */
        public TrialInfo getMaximum() {
            TrialInfo best = null;
            for (Iterator i = trials.values().iterator(); i.hasNext();) {
                TrialInfo t = (TrialInfo) i.next();
                if (best == null || t.cost > best.cost)
                    best = t;
            }
            return best;
        }

        /**
         * @return the mean of the trials
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
         * @return the trials sorted by increasing cost
         */
        public TrialInfo[] getSorted() {
            if (sorted == null) {
                sorted = (TrialInfo[]) trials.values().toArray(new TrialInfo[trials.size()]);
                Arrays.sort(sorted);
            }
            return sorted;
        }

        /**
         * @return the collection of trials
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
            return name + "@" + dateFormat.format(new Date(timeStamp));
        }

        /**
         * Returns this TrialCollection as an XML element.
         * 
         * @return XML element
         */
        public Element toXMLElement() {
            Element dis = new Element("trialCollection");
            dis.setAttribute("name", name);
            dis.setAttribute("timeStamp", Long.toString(timeStamp));
            for (Iterator i = trials.values().iterator(); i.hasNext();) {
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
            for (Iterator i = e.getContent().iterator(); i.hasNext();) {
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
        Map/* <OrderConstraint,ConstraintInfo> */infos;

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

            for (Iterator i = tc.getTrials().iterator(); i.hasNext();) {
                TrialInfo ti = (TrialInfo) i.next();
                Order o = ti.order;
                if (ti.cost >= BDDInferenceRule.LONG_TIME)
                    ((BDDSolver) solver).fbo.neverTryAgain(tc.getRule(solver), o);
                if (trans != null) o = trans.translate(o);
                Collection ocs = o.getConstraints();
                for (Iterator j = ocs.iterator(); j.hasNext();) {
                    OrderConstraint oc = (OrderConstraint) j.next();
                    c2Trials.add(oc, ti);
                }

            }

            for (Iterator i = c2Trials.keySet().iterator(); i.hasNext();) {
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
                out.println("Added trial collection: " + tc);
            }
        }

        public OrderInfo predict(Order o, OrderTranslator trans) {
            if (TRACE > 2) out.println("Predicting order "+o);
            if (trans != null) o = trans.translate(o);
            if (TRACE > 2) out.println("Translated into order "+o);
            double score = 0.;
            int numTrialCollections = 0, numTrials = 0;
            Collection cinfos = new LinkedList();
            for (Iterator i = o.getConstraints().iterator(); i.hasNext();) {
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
     * @return XML element
     */
    public Element toXMLElement() {
        Element constraintInfoCollection = new Element("constraintInfoCollection");
        for (Iterator i = constraintInfo.infos.entrySet().iterator(); i.hasNext();) {
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
     * @return XML element
     */
    public Element trialsToXMLElement() {
        Element trialCollections = new Element("trialCollections");
        if (solver.inputFilename != null)
            trialCollections.setAttribute("datalog", solver.inputFilename);
        for (Iterator i = allTrials.iterator(); i.hasNext();) {
            TrialCollection c = (TrialCollection) i.next();
            trialCollections.addContent(c.toXMLElement());
        }
        return trialCollections;
    }

    /**
     */
    public boolean hasOrdersToTry(List allVars, BDDInferenceRule ir) {
        // TODO: improve this code.
        int nTrials = getNumberOfTrials();
        if (nTrials != ir.lastTrialNum) {
            ir.lastTrialNum = nTrials;
            TrialGuess g = this.tryNewGoodOrder(null, allVars, ir, false);
            return g != null;
        } else {
            return false;
        }
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
            for (Iterator i = o.getConstraints().iterator(); i.hasNext();) {
                OrderConstraint oc = (OrderConstraint) i.next();
                // TODO: use a map from Pair to int instead of building String and doing linear search.
                String cName = oc.getFirst() + "," + oc.getSecond();
                OrderAttribute oa = (OrderAttribute) dataSet.attribute(cName);
                if (oa != null) {
                    d[oa.index()] = WekaInterface.getType(oc);
                } else {
                    //System.out.println("Warning: cannot find constraint "+oc+" order "+ti.order+" in dataset "+dataSet.relationName());
                    return null;
                }
            }
            d[d.length - 1] = cost;
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

        public TrialInfo getTrialInfo() { return ti; }

        public double getCost() {
            return value(numAttributes() - 1);
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
        
        public static TrialInstance cloneInstance(TrialInstance instance){
            return new TrialInstance(instance.weight(), instance.toDoubleArray(), instance.getOrder(), instance.getTrialInfo());
        }

    }

    // Since JDK1.4 only.
    public static final int compare(double d1, double d2) {
        if (d1 < d2)
            return -1; // Neither val is NaN, thisVal is smaller
        if (d1 > d2)
            return 1; // Neither val is NaN, thisVal is larger

        long thisBits = Double.doubleToLongBits(d1);
        long anotherBits = Double.doubleToLongBits(d2);

        return (thisBits == anotherBits ? 0 : // Values are equal
                (thisBits < anotherBits ? -1 : // (-0.0, 0.0) or (!NaN, NaN)
                        1)); // (0.0, -0.0) or (NaN, !NaN)
    }

    public static class Discretization {
        double[] cutPoints;

        TrialInstances[] buckets;

        public Discretization(double[] cutPoints, TrialInstances[] buckets) {
            this.cutPoints = cutPoints;
            this.buckets = buckets;
        }
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

        public Discretization threshold(double thres) {
            return threshold(thres, this.classIndex());
        }

        public Discretization threshold(double thres, int index) {
            if (numInstances() == 0) return null;
            FastVector clusterValues = new FastVector(2);
            TrialInstances[] buckets = new TrialInstances[2];
            FastVector origAttributes = (FastVector) this.m_Attributes.copy(); //shared across all buckets

            buckets[0] = new TrialInstances(this.m_RelationName + "_bucket_0", origAttributes, 30);
            buckets[1] = new TrialInstances(this.m_RelationName + "_bucket_1", origAttributes, 30);
            double[] cutPoint = new double[1];
            cutPoint[0] = thres;

            clusterValues.addElement("<" + format(thres));
            clusterValues.addElement(">" + format(thres));
            weka.core.Attribute a = new weka.core.Attribute("costThres" + format(thres), clusterValues);
            m_Attributes.setElementAt(a, index);
            setIndex(a, index);
            Enumeration f = m_Instances.elements();
            while (f.hasMoreElements()) {
                TrialInstance old_i = (TrialInstance) f.nextElement();
                double oldVal = old_i.value(index);
                double val = oldVal < thres ? 0 : 1;
                //deep copy order and trial?
                double[] old_i_arr = old_i.toDoubleArray();
                double[] old_i_copy = new double[old_i_arr.length];
                System.arraycopy(old_i_arr, 0, old_i_copy, 0, old_i_arr.length);
                buckets[(int) val].add(new TrialInstance(old_i.weight(), old_i_copy, old_i.getOrder(), old_i.getTrialInfo()));
                old_i.setValue(index, val);
            }

            return new Discretization(cutPoint, buckets);
        }

        public Discretization discretize(double power) {
            int numBins = (int) Math.pow(numInstances(), power);
            return discretize(new MyDiscretize(power), numBins, this.classIndex());
        }

        public Discretization discretize(Discretize d, int numBins, int index) {
            if (numInstances() <= 1) return null;
            try {
                int classIndex = this.classIndex();
                setClassIndex(-1); // clear class instance for discretization.
                d.setAttributeIndices(Integer.toString(index+1)); // RANGE IS 1-BASED!!!
                d.setInputFormat(this); // NOTE: this must be LAST because it calls setUpper
                Instances newInstances;
                newInstances = Filter.useFilter(this, d);
                if (d.getFindNumBins()) numBins = d.getBins();
                TrialInstances[] buckets = new TrialInstances[numBins];

                FastVector origAttributes = (FastVector) this.m_Attributes.copy(); //shared across all buckets
                for (int i = 0; i < numBins; ++i) {
                    buckets[i] = new TrialInstances(this.m_RelationName + "_bucket_" + i, origAttributes, this.numInstances() / numBins);
                    buckets[i].setClassIndex(classIndex);
                }
                double[] result = d.getCutPoints(index);
                weka.core.Attribute a = makeBucketAttribute(numBins);
                m_Attributes.setElementAt(a, index);
                setIndex(a, index);
                Enumeration e = newInstances.enumerateInstances();
                Enumeration f = m_Instances.elements();
                while (e.hasMoreElements()) {
                    Instance new_i = (Instance) e.nextElement();
                    TrialInstance old_i = (TrialInstance) f.nextElement();
                    double val = new_i.value(index);
                    double[] old_i_arr = old_i.toDoubleArray();
                    double[] old_i_copy = new double[old_i_arr.length];
                    System.arraycopy(old_i_arr, 0, old_i_copy, 0, old_i_arr.length);
                    buckets[(int) val].add(new TrialInstance(old_i.weight(), old_i_copy, old_i.getOrder(), old_i.getTrialInfo()));
                    old_i.setValue(index, val);
                }
                setClassIndex(classIndex); // reset class index.
                Assert._assert(!f.hasMoreElements());
                return new Discretization(result, buckets);
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
                Assert.UNREACHABLE("weka sucks: " + x);
            }
        }
        public TrialInstances infoClone(){
            return new TrialInstances(this.m_RelationName, this.m_Attributes, this.numInstances());
        }
        
        public Instances resample(Random random) {
            TrialInstances newData = infoClone();
            while (newData.numInstances() < numInstances()) {
              newData.add(instance(random.nextInt(numInstances())));
            }
            newData.setClassIndex(classIndex());
            return newData;
          }
    }

    static weka.core.Attribute makeBucketAttribute(int numClusters) {
        FastVector clusterValues = new FastVector(numClusters);
        for (int i = 0; i < numClusters; ++i)
            clusterValues.addElement(Integer.toString(i));
        return new weka.core.Attribute("costBucket", clusterValues);
    }

    static void addToInstances(Instances data, TrialCollection tc, OrderTranslator t) {
        if (tc.size() == 0) return;
        double best;
        if (tc.getMinimum().isMax()) best = 1;
        else best = (double) tc.getMinimum().cost + 1;
        for (Iterator j = tc.trials.values().iterator(); j.hasNext();) {
            TrialInfo ti = (TrialInfo) j.next();
            double score = (double) (ti.cost + 1) / best;
            Order o = t == null ? ti.order : t.translate(ti.order);
            if (o.numberOfElements() <= 1) continue;
            TrialInstance tinst = TrialInstance.construct(ti, o, score, data);
            if (tinst != null) data.add(tinst);
        }
        
      
    }

    TrialInstances buildVarInstances(InferenceRule ir, List allVars) {
        FastVector attributes = new FastVector();
        WekaInterface.addAllPairs(attributes, allVars);
        attributes.addElement(new weka.core.Attribute("score"));
        int capacity = 30;
        OrderTranslator filter = new FilterTranslator(allVars);
        TrialInstances data = new TrialInstances("Var Ordering Constraints", attributes, capacity);
        if (allVars.size() <= 1) return data;
        for (Iterator i = allTrials.iterator(); i.hasNext();) {
            TrialCollection tc2 = (TrialCollection) i.next();
            InferenceRule ir2 = tc2.getRule(solver);
            if (ir != ir2) continue;
            addToInstances(data, tc2, filter);
        }
        data.setClassIndex(data.numAttributes() - 1);
        return data;
    }

    TrialInstances buildAttribInstances(InferenceRule ir, List allVars) {
        List allAttribs = VarToAttribMap.convert(allVars, ir);
        if (TRACE > 1) out.println("Attribs: "+allAttribs);
        FastVector attributes = new FastVector();
        WekaInterface.addAllPairs(attributes, allAttribs);
        attributes.addElement(new weka.core.Attribute("score"));
        int capacity = 30;
        TrialInstances data = new TrialInstances("Attribute Ordering Constraints", attributes, capacity);
        if (allAttribs.size() <= 1) return data;
        for (Iterator i = allTrials.iterator(); i.hasNext();) {
            TrialCollection tc2 = (TrialCollection) i.next();
            InferenceRule ir2 = tc2.getRule(solver);
            OrderTranslator t = new VarToAttribTranslator(ir2);
            t = new OrderTranslator.Compose(t, new FilterTranslator(allAttribs));
            addToInstances(data, tc2, t);
        }
        data.setClassIndex(data.numAttributes() - 1);
        return data;
    }

    TrialInstances buildDomainInstances(InferenceRule ir, List allVars) {
        List allDomains = AttribToDomainMap.convert(VarToAttribMap.convert(allVars, ir));
        if (TRACE > 1) out.println("Domains: "+allDomains);
        FastVector attributes = new FastVector();
        WekaInterface.addAllPairs(attributes, allDomains);
        attributes.addElement(new weka.core.Attribute("score"));
        int capacity = 30;
        TrialInstances data = new TrialInstances("Domain Ordering Constraints", attributes, capacity);
        if (allDomains.size() <= 1) return data;
        for (Iterator i = allTrials.iterator(); i.hasNext();) {
            TrialCollection tc2 = (TrialCollection) i.next();
            InferenceRule ir2 = tc2.getRule(solver);
            OrderTranslator t = new VarToAttribTranslator(ir2);
            t = new OrderTranslator.Compose(t, AttribToDomainTranslator.INSTANCE);
            t = new OrderTranslator.Compose(t, new FilterTranslator(allDomains));
            addToInstances(data, tc2, t);
        }
        data.setClassIndex(data.numAttributes() - 1);
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
            out.println(cClassName + ": " + x.getLocalizedMessage());
            return null;
        }
        return classifier;
    }

    public final static int WEIGHT_WINDOW_SIZE = Integer.MAX_VALUE;

    public final static double DECAY_FACTOR = -.1;

    public double computeWeight(int type, TrialInstances instances) {
        int numTrials = 0;
        double total = 0;
        int losses = 0;
        double weight = 1;
        for (int i = instances.numInstances() - 1; i >= 0 && numTrials < WEIGHT_WINDOW_SIZE; --i) {
            TrialInstance instance = (TrialInstance) instances.instance(i);
            double trueCost = instance.getCost();

            TrialPrediction pred = instance.getTrialInfo().pred;
            double predCost = pred.predictions[type][TrialPrediction.LOW];
            double dev = pred.predictions[type][TrialPrediction.HIGH];

            if(predCost == -1) continue;
            double trialWeight = Math.exp(DECAY_FACTOR * numTrials);
            if (trueCost < predCost - dev || trueCost > predCost + dev) {
                losses += trialWeight;
            }
            total += trialWeight;
            ++numTrials;
        }
        if (numTrials != 0) {
            weight = 1 - losses / (double) total;
        }
        return weight;
    }

    public void adjustWeights(TrialInstances vData, TrialInstances aData, TrialInstances dData) {
        if (vData != null)
            varClassWeight = computeWeight(TrialPrediction.VARIABLE, vData);
        if (aData != null)
            attrClassWeight = computeWeight(TrialPrediction.ATTRIBUTE, aData);
        if (dData != null)
            domClassWeight = computeWeight(TrialPrediction.DOMAIN, dData);
    }

    public static int NUM_CV_FOLDS = 10;

    public double leaveOneOutCV(Instances data, String cClassName) {
        return cvError(data.numInstances(), data, cClassName);
    }

    /**
     * @param data
     * @param cClassName
     * @return Cross validation with number of folds as set by NUM_CV_FOLDS;
     */
    public double constFoldCV(Instances data, String cClassName) {
        return cvError(NUM_CV_FOLDS, data, cClassName);
    }

    public double cvError(int numFolds, Instances data0, String cClassName) {
        if (data0.numInstances() < numFolds)
            return Double.NaN; //more folds than elements
        if (numFolds == 0)
            return Double.NaN; // no folds
        if (data0.numInstances() == 0)
            return 0; //no instances

        Instances data = new Instances(data0);
        //data.randomize(new Random(System.currentTimeMillis()));
        data.stratify(numFolds);
        Assert._assert(data.classAttribute() != null);
        double[] estimates = new double[numFolds];
        for (int i = 0; i < numFolds; ++i) {
            Instances trainData = data.trainCV(numFolds, i);
            Assert._assert(trainData.classAttribute() != null);
            Assert._assert(trainData.numInstances() != 0, "Cannot train classifier on 0 instances.");

            Instances testData = data.testCV(numFolds, i);
            Assert._assert(testData.classAttribute() != null);
            Assert._assert(testData.numInstances() != 0, "Cannot test classifier on 0 instances.");

            int temp = TRACE;
            TRACE = 0;
            Classifier classifier = buildClassifier(cClassName, trainData);
            TRACE = temp;
            int count = testData.numInstances();
            double loss = 0;
            double sum = 0;
            for (Enumeration e = testData.enumerateInstances(); e.hasMoreElements();) {
                Instance instance = (Instance) e.nextElement();
                Assert._assert(instance.classAttribute() != null && instance.classAttribute() == trainData.classAttribute());
                Assert._assert(instance != null);
                try {
                    double testClass = classifier.classifyInstance(instance);
                    double weight = instance.weight();
                    if (testClass != instance.classValue())
                        loss += weight;
                    sum += weight;
                } catch (Exception ex) {
                    out.println("Exception while classifying: " + instance + "\n" + ex);
                }
            }
            estimates[i] = 1 - loss / sum;
        }
        double average = 0;
        for (int i = 0; i < numFolds; ++i)
            average += estimates[i];

        return average / numFolds;
    }

    public TrialInstances binarize(double classValue, TrialInstances data) {
        TrialInstances newInstances = data.infoClone();
        weka.core.Attribute newAttr = makeBucketAttribute(2);
        TrialInstances.setIndex(newAttr, newInstances.classIndex());
        newInstances.setClass(newAttr);
        newInstances.setClassIndex(data.classIndex());
        for (Enumeration e = data.enumerateInstances(); e.hasMoreElements();) {
            TrialInstance instance = (TrialInstance) e.nextElement();
            TrialInstance newInstance = TrialInstance.cloneInstance(instance);
            newInstance.setDataset(newInstances);
            if (instance.classValue() <= classValue) {
                newInstance.setClassValue(0);
            } else {
                newInstance.setClassValue(1);
            }
            newInstances.add(newInstance);
        }
        return newInstances;
    }

    public static double RMS(double vProb, double vCent, double aProb, double aCent, double dProb, double dCent) {
        double vDiff = Math.abs(vProb - vCent);
        double aDiff = Math.abs(aProb - aCent);
        double dDiff = Math.abs(dProb - dCent);
        return Math.sqrt(((vDiff * vDiff) + (aDiff * aDiff) + (dDiff * dDiff)) / 3);

    }

    public static boolean DISCRETIZE1 = true;
    public static boolean DISCRETIZE2 = true;
    public static boolean DISCRETIZE3 = true;
    public static String CLASSIFIER1 = "net.sf.bddbddb.order.MyId3";
    public static String CLASSIFIER2 = "net.sf.bddbddb.order.MyId3";
    public static String CLASSIFIER3 = "net.sf.bddbddb.order.MyId3";
    public static String CPE = "net.sf.bddbddb.order.BaggedId3";
    
    public void neverTryAgain(InferenceRule ir, Order o) {
          if (true) {
            if (TRACE > 2) out.println("For rule"+ir.id+", never trying order "+o+" again.");
            neverAgain.add(ir, o);
        }
    }

    MultiMap neverAgain = new GenericMultiMap();

    public double varClassWeight = 1;
    public double attrClassWeight = 1;
    public double domClassWeight = 1;
    public static int DOMAIN_THRESHOLD = 1000;
    public static int NO_CLASS = -1;
    public static int NO_CLASS_SCORE = -1;
    public boolean PROBABILITY = false;
    void dumpClassifierInfo(String name, Classifier c, Instances data) {
        BufferedWriter w = null;
        try {
            w = new BufferedWriter(new FileWriter(name));
            w.write("Classifier \"name\":\n");
            w.write("Based on data from "+data.numInstances()+" instances:\n");
            for (Enumeration e = data.enumerateInstances(); e.hasMoreElements(); ) {
                Instance i = (Instance) e.nextElement();
                if (i instanceof TrialInstance) {
                    TrialInstance ti = (TrialInstance) i;
                    InferenceRule ir = ti.ti.collection.getRule(solver);
                    w.write("    "+ti.ti.collection.name+" "+ti.getOrder());
                    if (!ti.getOrder().equals(ti.ti.order))
                        w.write(" ("+ti.ti.order+")");
                    if (ti.isMaxTime()) {
                        w.write(" MAX TIME\n");
                    } else {
                        w.write(" "+format(ti.getCost())+" ("+ti.ti.cost+" ms)\n");
                    }
                } else {
                    w.write("    "+i+"\n");
                }
            }
            w.write(c.toString());
            w.write("\n");
        } catch (IOException x) { 
            System.err.println("IO Exception occurred writing \""+name+"\": "+x);
        } finally {
            if (w != null) try { w.close(); } catch (IOException _) { }
        }
    }
    
    void dumpTrialGuessInfo(String name) {
        BufferedWriter w = null;
        try {
            w = new BufferedWriter(new FileWriter(name, true));
            w.write("Classifier \"name\":\n");
            w.write("\n");
        } catch (IOException x) { 
            System.err.println("IO Exception occurred writing \""+name+"\": "+x);
        } finally {
            if (w != null) try { w.close(); } catch (IOException _) { }
        }
    }
    
    public TrialGuess tryNewGoodOrder(TrialCollection tc, List allVars, InferenceRule ir,
            boolean returnBest) {
        return tryNewGoodOrder(tc, allVars, ir, null, returnBest);
    }
    
    public TrialGuess tryNewGoodOrder(TrialCollection tc, List allVars, InferenceRule ir,
            Order chosenOne,
            boolean returnBest) {

        // Build instances based on the experimental data.
        TrialInstances vData, aData, dData;
        vData = buildVarInstances(ir, allVars);
        aData = buildAttribInstances(ir, allVars);
        dData = buildDomainInstances(ir, allVars);

        // Readjust the weights using an exponential decay factor.
        adjustWeights(vData, aData, dData);
        Discretization vDis = null, aDis = null, dDis = null;

       // Discretize the experimental data.  null if there is no data.
        if (DISCRETIZE1) vDis = vData.discretize(.5);
        if (DISCRETIZE2) aDis = aData.discretize(.25);
        if (DISCRETIZE3) dDis = dData.threshold(DOMAIN_THRESHOLD);
        
        // Calculate the accuracy of each classifier using cv folds.
        long vCTime = System.currentTimeMillis();
        double vConstCV = -1; //constFoldCV(vData, CLASSIFIER1);
        vCTime = System.currentTimeMillis() - vCTime;

        long aCTime = System.currentTimeMillis();
        double aConstCV = -1; //constFoldCV(aData, CLASSIFIER2);
        aCTime = System.currentTimeMillis() - aCTime;
        
        long dCTime = System.currentTimeMillis();
        double dConstCV = -1; //constFoldCV(dData, CLASSIFIER3);
        dCTime = System.currentTimeMillis() - dCTime;
        
        long vLTime = System.currentTimeMillis();
        double vLeaveCV = -1; //leaveOneOutCV(vData, CLASSIFIER1);
        vLTime = System.currentTimeMillis() - vLTime;
        
        long aLTime = System.currentTimeMillis();
        double aLeaveCV = -1; //leaveOneOutCV(aData, CLASSIFIER2);
        aLTime = System.currentTimeMillis() - aLTime;
        
        long dLTime = System.currentTimeMillis();
        double dLeaveCV = -1; //leaveOneOutCV(dData, CLASSIFIER3);
        dLTime = System.currentTimeMillis() - dLTime;
        
        if (TRACE > 1) {
            out.println(" Var data points: " + vData.numInstances());
            out.println(" Var Classifier " + NUM_CV_FOLDS + " fold CV Score: " + vConstCV + " took " + vCTime + " ms");
           // out.println(" Var Classifier leave one out CV Score: " + vLeaveCV + " took " + vLTime + " ms");
            out.println(" Var Classifier Weight: " + varClassWeight);
            //out.println(" Var data points: "+vData);
            out.println(" Attrib data points: " + aData.numInstances());
            out.println(" Attrib Classifier " + NUM_CV_FOLDS + " fold CV Score : " + aConstCV + " took " + aCTime + " ms");
            //out.println(" Attrib Classifier leave one out CV Score: " + aLeaveCV + " took " + aLTime + " ms");
            out.println(" Attrib Classifier Weight: " + attrClassWeight);
            //out.println(" Attrib data points: "+aData);
            out.println(" Domain data points: " + dData.numInstances());
            out.println(" Domain Classifier " + NUM_CV_FOLDS + " fold CV Score: " + dConstCV + " took " + dCTime + " ms");
            //out.println(" Attrib Classifier leave one out CV Score: " + dLeaveCV + " took " + dLTime + " ms");
            out.println(" Domain Classifier Weight: " + domClassWeight);
            //out.println(" Domain data points: "+dData);

        }

        // Build the classifiers.
        Classifier vClassifier = null, aClassifier = null, dClassifier = null;
        if (vData.numInstances() > 0)
            vClassifier = buildClassifier(CLASSIFIER1, vData);
        if (aData.numInstances() > 0)
            aClassifier = buildClassifier(CLASSIFIER2, aData);
        if (dData.numInstances() > 0)
            dClassifier = buildClassifier(CLASSIFIER3, dData);

        if (DUMP_CLASSIFIER_INFO) {
            String baseName = solver.getBaseName()+"_rule"+ir.id;
            if (vClassifier != null)
                dumpClassifierInfo(baseName+"_vclassifier", vClassifier, vData);
            if (aClassifier != null)
                dumpClassifierInfo(baseName+"_aclassifier", aClassifier, aData);
            if (dClassifier != null)
                dumpClassifierInfo(baseName+"_dclassifier", dClassifier, dData);
            try {
                out_t = new PrintStream(new FileOutputStream(baseName+"_trials"));
            } catch (IOException x) {
                System.err.println("Error while opening file: "+x);
            }
        } else {
            out_t = null;
        }
        
        if (TRACE > 2) {
            out.println("Var classifier: " + vClassifier);
            out.println("Attrib classifier: " + aClassifier);
            out.println("Domain classifier: " + dClassifier);
        }

        // Calculate the mean value of each of the discretized buckets.
        double[] vBucketMeans = new double[vDis == null ? 0 : vDis.buckets.length];
        double[] aBucketMeans = new double[aDis == null ? 0 : aDis.buckets.length];
        double[] dBucketMeans = new double[dDis == null ? 0 : dDis.buckets.length];
        if(TRACE > 2) out.print("Var Bucket Means: ");
        for (int i = 0; i < vBucketMeans.length; ++i) {
            if (vDis.buckets[i].numInstances() == 0)
                vBucketMeans[i] = Double.MAX_VALUE;
            else
                vBucketMeans[i] = vDis.buckets[i].meanOrMode(vDis.buckets[i].classIndex());
            if(TRACE > 2) out.print(vBucketMeans[i] + " ");
        }
        if (TRACE > 2) {
            out.println();
            out.print("Attr Bucket Means: ");
        }
        for (int i = 0; i < aBucketMeans.length; ++i) {
            if (aDis.buckets[i].numInstances() == 0)
                aBucketMeans[i] = Double.MAX_VALUE;
            else
                aBucketMeans[i] = aDis.buckets[i].meanOrMode(aData.classIndex());
            if(TRACE > 2) out.print(aBucketMeans[i] + " ");
        }
        if (TRACE > 2) {
            out.println();
            out.print("Domain Bucket Means: ");
        }
        for (int i = 0; i < dBucketMeans.length; ++i) {
            if (dDis.buckets[i].numInstances() == 0)
                dBucketMeans[i] = Double.MAX_VALUE;
            else
                dBucketMeans[i] = dDis.buckets[i].meanOrMode(dData.classIndex());
            if(TRACE > 2) out.print(dBucketMeans[i] + " ");
        }
        if(TRACE > 2) out.println();

        // Build multi-map from attributes/domains to variables.
        MultiMap a2v, d2v;
        a2v = new GenericMultiMap();
        d2v = new GenericMultiMap();
        for (Iterator i = allVars.iterator(); i.hasNext();) {
            Variable v = (Variable) i.next();
            Attribute a = (Attribute) ir.getAttribute(v);
            if (a != null) {
                a2v.add(a, v);
                d2v.add(a.getDomain(), v);
            }
        }
        
        Set candidates = null;
        Collection sel = null;
        if (chosenOne == null) {
            boolean addNullValues = !returnBest;
            // Grab the best from the classifiers and try to build an optimal order.
            if (!returnBest) candidates = new LinkedHashSet();
            Collection never = neverAgain.getValues(ir);
            MyId3 v = (MyId3) vClassifier, a = (MyId3) aClassifier, d = (MyId3) dClassifier;
            int end = 5;
            // Use only top half of buckets.
            int vBuckets = vDis == null ? 1 : vDis.buckets.length / 2 + 1;
            int aBuckets = aDis == null ? 1 : aDis.buckets.length / 2 + 1;
            int dBuckets = dDis == null ? 1 : dDis.buckets.length / 2 + 1;
            double max = (vBucketMeans.length != 0 ? vBucketMeans[vBucketMeans.length-1] : 0);
            max += (aBucketMeans.length != 0 ? aBucketMeans[aBucketMeans.length-1] : 0);
            max += (dBucketMeans.length != 0 ? dBucketMeans[dBucketMeans.length-1] : 0);
            boolean[][][] done = new boolean[vBuckets+1][aBuckets+1][dBuckets+1];
        outermost:
            while (candidates == null || candidates.size() < CANDIDATE_SET_SIZE) {
                int numV = Math.min(end, vBuckets);
                int numA = Math.min(end, aBuckets);
                int numD = Math.min(end, dBuckets);
                if (true && end > vBuckets && end > aBuckets && end > dBuckets) {
                    // Also include the "empty" classification for all of them.
                    numV++; numA++; numD++;
                }
                int maxNum = addNullValues ? ((numV+1)*(numA+1)*(numD+1)) : (numV*numA*numD);
                double[][] combos = new double[maxNum][];
                int p = 0;
                int start = addNullValues ? -1 : 0; 
                for (int vi = start; vi < numV; ++vi) {
                    for (int ai = start; ai < numA; ++ai) {
                        for (int di = 0; di < numD; ++di) { // don't do nulls for domain classifier.
                            double vScore, aScore, dScore;
                            double nullScore = 1;
                            if (vi == -1) vScore = nullScore;
                            else if (vi < vBuckets && vi < vBucketMeans.length) vScore = vBucketMeans[vi];
                            else vScore = max;
                            if (ai == -1) aScore = nullScore;
                            else if (ai < aBuckets && ai < aBucketMeans.length) aScore = aBucketMeans[ai];
                            else aScore = max;
                            if (di == -1) dScore = nullScore;
                            else if (di < dBuckets && di < dBucketMeans.length) dScore = dBucketMeans[di];
                            else dScore = max;
                            double score = varClassWeight * vScore;
                            score += attrClassWeight * aScore;
                            score += domClassWeight * dScore;
                            double[] result = new double[] { score, vi==-1?Double.NaN:vi,
                                                                    ai==-1?Double.NaN:ai,
                                                                    di==-1?Double.NaN:di };
                            if (TRACE > 2) {
                                out.println("Score for v="+vi+" a="+ai+" d="+di+": "+format(score));
                            }
                            combos[p++] = result;
                        }
                    }
                }
                Arrays.sort(combos, 0, p, new Comparator() {
                    public int compare(Object arg0, Object arg1) {
                        double[] a = (double[]) arg0;
                        double[] b = (double[]) arg1;
                        return FindBestDomainOrder.compare(a[0], b[0]);
                    }
                });
                for (int z = 0; z < p; ++z) {
                    double bestScore = combos[z][0];
                    double vClass = combos[z][1]; int vi = (int) vClass;
                    double aClass = combos[z][2]; int ai = (int) aClass;
                    double dClass = combos[z][3]; int di = (int) dClass;
                    // If one of them reaches the highest index, we need to break.
                    if (vi == numV-1 && end <= vBuckets ||
                        ai == numA-1 && end <= aBuckets ||
                        di == numD-1 && end <= dBuckets) {
                        if (TRACE > 1) out.println("reached end ("+vi+","+ai+","+di+"), trying again with a higher cutoff.");
                        break;
                    }
                    if (!Double.isNaN(vClass) && !Double.isNaN(aClass) && !Double.isNaN(dClass)) {
                        if (done[vi][ai][di]) continue;
                        done[vi][ai][di] = true;
                    } else {
                        addNullValues = false;
                    }
                    if (vi == vBuckets) vClass = -1; // any
                    if (ai == aBuckets) aClass = -1;
                    if (di == dBuckets) dClass = -1;
                    if (out_t != null) out_t.println("v="+vClass+" a="+aClass+" d="+dClass+": "+format(bestScore));
                    Collection ocss = tryConstraints(v, vClass, vData, a, aClass, aData, d, dClass, dData, a2v, d2v);
                    if (ocss == null || ocss.isEmpty()) {
                        if (out_t != null) out_t.println("Constraints cannot be combined.");
                        continue;
                    }
                    for (Iterator i = ocss.iterator(); i.hasNext(); ) {
                        OrderConstraintSet ocs = (OrderConstraintSet) i.next();
                        if (out_t != null) out_t.println("Constraints: "+ocs);
                        if (returnBest) {
                            TrialGuess guess = genGuess(ocs, bestScore, allVars, bestScore, vClass, aClass, dClass,
                                vDis, aDis, dDis, tc, never);
                            if (guess != null) {
                                if (TRACE > 1) out.println("Best Guess: "+guess);
                                return guess;
                            }
                        } else {
                            // Add these orders to the collection.
                            genOrders(ocs, allVars, tc == null ? null : tc.trials.keySet(), never, candidates);
                            if (candidates.size() >= CANDIDATE_SET_SIZE) break outermost;
                        }
                    }
                }
                if (end > vBuckets && end > aBuckets && end > dBuckets) {
                    if (TRACE > 1) out.println("Reached end, no more possible guesses!");
                    if (false) {
                        // TODO: we can do something better here!
                        OrderIterator i = new OrderIterator(allVars);
                        while (i.hasNext()) {
                            Order o_v = i.nextOrder();
                            if (tc != null && tc.contains(o_v)) continue;
                            if (never != null && never.contains(o_v)) continue;
                            if (TRACE > 1) out.println("Just trying "+o_v);
                            if (returnBest) {
                                sel = Collections.singleton(o_v);
                                break outermost;
                            } else {
                                // Add this order to the collection.
                                if (TRACE > 1) out.println("Adding to candidate set: "+o_v);
                                candidates.add(o_v);
                                if (candidates.size() >= CANDIDATE_SET_SIZE) break outermost;
                            }
                        }
                    }
                    if (returnBest) {
                        return null;
                    }
                    break outermost;
                }
                end *= 2;
                if (TRACE > 1) out.println("Cutoff is now "+end);
            }
        } else {
            sel = Collections.singleton(chosenOne);
        }
        
        boolean force = (tc != null && tc.size() < 2) ||
            vData.numInstances() < INITIAL_SET ||
            aData.numInstances() < INITIAL_SET ||
            dData.numInstances() < INITIAL_SET;
        
        if (!returnBest)
            sel = selectOrder(candidates, vData, aData, dData, ir, force);
        if (sel == null || sel.isEmpty()) return null;
        Order o_v = (Order) sel.iterator().next();
        try {
            OrderTranslator v2a = new VarToAttribTranslator(ir);
            OrderTranslator a2d = AttribToDomainTranslator.INSTANCE;
            double vClass = 0, aClass = 0, dClass = 0;
            if (vClassifier != null) {
                OrderInstance vInst = OrderInstance.construct(o_v, vData);
                vClass = vClassifier.classifyInstance(vInst);
            }
            Order o_a = v2a.translate(o_v);
            if (aClassifier != null) {
                OrderInstance aInst = OrderInstance.construct(o_a, aData);
                aClass = aClassifier.classifyInstance(aInst);
            }
            Order o_d = a2d.translate(o_a);
            if (dClassifier != null) {
                OrderInstance dInst = OrderInstance.construct(o_d, dData);
                dClass = dClassifier.classifyInstance(dInst);
            }
            int vi = (int) vClass, ai = (int) aClass, di = (int) dClass;
            double vScore = 0, aScore = 0, dScore = 0;
            if (vi < vBucketMeans.length) vScore = vBucketMeans[vi];
            if (ai < aBucketMeans.length) aScore = aBucketMeans[ai];
            if (di < dBucketMeans.length) dScore = dBucketMeans[di];
            double score = varClassWeight * vScore;
            score += attrClassWeight * aScore;
            score += domClassWeight * dScore;
            return genGuess(o_v, score, vClass, aClass, dClass, vDis, aDis, dDis);
        } catch (Exception x) {
            x.printStackTrace();
            Assert.UNREACHABLE(x.toString());
            return null;
        }
    }

    public static int CANDIDATE_SET_SIZE = 500;
    
    public static boolean LV = false;
    public Collection selectOrder(Collection orders,
            TrialInstances vData, TrialInstances aData, TrialInstances dData, InferenceRule ir, boolean force) {
        
        if (TRACE > 1) out.println("Selecting an order from a candidate set of "+orders.size()+" orders.");
        if (TRACE > 2) out.println("Orders: "+orders);
        return LV ? localVariance(orders, vData, aData, dData, ir) :
            uncertaintySample(orders, vData,aData, dData, ir, force);
        
    }
    
    public static double UNCERTAINTY_THRESHOLD = 0.25;
    public static boolean WEIGHT_UNCERTAINTY_SAMPLE = false;
    public static double VCENT = .5, ACENT = .5, DCENT = 1;
    public static double MAX_SCORE = 1 / Math.sqrt(2); //for these centers
     public Collection uncertaintySample(Collection orders,
             TrialInstances vData, TrialInstances aData, TrialInstances dData, InferenceRule ir, boolean force) {
        ClassProbabilityEstimator vCPE = null, aCPE  = null, dCPE = null;
        vCPE = (ClassProbabilityEstimator) buildClassifier(CPE, binarize(0, vData));
        aCPE = (ClassProbabilityEstimator) buildClassifier(CPE, binarize(0, aData));
        dCPE = (ClassProbabilityEstimator) buildClassifier(CPE, binarize(0, dData));
        
        OrderTranslator v2a = new VarToAttribTranslator(ir);
        OrderTranslator a2d = AttribToDomainTranslator.INSTANCE;
        
        Order best = null;
        double bestScore =Double.POSITIVE_INFINITY;
        double [] distribution = new double[orders.size()];
        double normalFact = 0;
        Order [] orderArr = new Order[orders.size()];
        int i = 0;
        for (Iterator it = orders.iterator(); it.hasNext(); ++i){
            Order o_v = (Order) it.next();
            orderArr[i] = o_v;
            OrderInstance vInstance = TrialInstance.construct(o_v, vData);
            Order o_a = v2a.translate(o_v);
            OrderInstance aInstance = TrialInstance.construct(o_a, aData);
            Order o_d = a2d.translate(o_a);
            OrderInstance dInstance = TrialInstance.construct(o_d, dData);
            
            double vScore = vCPE != null ? vCPE.classProbability(vInstance, 0) : VCENT;
            double aScore = aCPE != null ? aCPE.classProbability(aInstance, 0) : ACENT;
            double dScore = dCPE != null ? dCPE.classProbability(dInstance, 0) : DCENT;
            
            double score = RMS(vScore, VCENT, aScore, ACENT, dScore, DCENT);
            distribution[i] = MAX_SCORE - score;
            normalFact += MAX_SCORE - score;
            
            if (score < bestScore) {
                if (TRACE > 1) out.println("Uncertain order "+o_v+" score: "+format(score)+" (v="+format(vScore)+",a="+format(aScore)+",d="+format(dScore)+")");
                bestScore = score;
                best = o_v;
            }
        }
        Collection ordersToTry = new LinkedList();
        if (force || bestScore < UNCERTAINTY_THRESHOLD) {
            if (WEIGHT_UNCERTAINTY_SAMPLE) {
                return sample(orderArr, distribution, normalFact);
            }
            ordersToTry.add(best);
        }
        return ordersToTry;
    }

     public static int INITIAL_SET = 10;

    public static int NUM_LV_ESTIMATORS = 10;
    public static Random random = new Random(System.currentTimeMillis());
    public Collection localVariance(Collection orders, TrialInstances vData, TrialInstances aData, TrialInstances dData, InferenceRule ir) {
        ClassProbabilityEstimator [] vEstimators = new ClassProbabilityEstimator[NUM_LV_ESTIMATORS];
        ClassProbabilityEstimator [] aEstimators = new ClassProbabilityEstimator[NUM_LV_ESTIMATORS];
        ClassProbabilityEstimator [] dEstimators = new ClassProbabilityEstimator[NUM_LV_ESTIMATORS];
        
        for(int i = 0; i < NUM_LV_ESTIMATORS; ++i){
            TrialInstances vBootData = (TrialInstances) vData.resample(random);
            TrialInstances aBootData = (TrialInstances) aData.resample(random);
            TrialInstances dBootData = (TrialInstances) dData.resample(random);
            vEstimators[i] = (ClassProbabilityEstimator) buildClassifier(CPE, binarize(0, vBootData));
            aEstimators[i] = (ClassProbabilityEstimator) buildClassifier(CPE, binarize(0, aBootData));
            dEstimators[i] = (ClassProbabilityEstimator) buildClassifier(CPE, binarize(0, dBootData));
        }
        
        double [] distribution = new double[orders.size()];
        Order[] orderArr = new Order[orders.size()];

        double normalFact = 0;
        double [][] estimates = new double[NUM_LV_ESTIMATORS + 1][3];
        
        OrderTranslator v2a = new VarToAttribTranslator(ir);
        OrderTranslator a2d = AttribToDomainTranslator.INSTANCE;
        
        int i = 0;
        for(Iterator it = orders.iterator(); it.hasNext(); ++i){
            Order o_v = (Order) it.next();
            //a little sketchy, since this is different data but it should work
            OrderInstance vInstance = TrialInstance.construct(o_v, vData);
            Order o_a = v2a.translate(o_v);
            OrderInstance aInstance = TrialInstance.construct(o_a, aData);
            Order o_d = a2d.translate(o_a);
            OrderInstance dInstance = TrialInstance.construct(o_d, dData);
            
            orderArr[i] = o_v;
            estimates[NUM_LV_ESTIMATORS][0] = 0;
            estimates[NUM_LV_ESTIMATORS][1] = 0;
            estimates[NUM_LV_ESTIMATORS][2] = 0;
            for(int j = 0; j < NUM_LV_ESTIMATORS; ++j){
               estimates[j][0] = vEstimators[j] != null ? vEstimators[j].classProbability(vInstance,0) : 0.5;
               estimates[j][1] = aEstimators[j] != null ? aEstimators[j].classProbability(aInstance,0) : 0.5;
               estimates[j][2] = dEstimators[j] != null ? dEstimators[j].classProbability(dInstance,0) : 0.5;
               estimates[NUM_LV_ESTIMATORS][0] += vEstimators[j] != null ? estimates[j][0] : 0;
               estimates[NUM_LV_ESTIMATORS][1] += aEstimators[j] != null ? estimates[j][1] : 0;
               estimates[NUM_LV_ESTIMATORS][2] += dEstimators[j] != null ? estimates[j][2] : 0;
            }
            estimates[NUM_LV_ESTIMATORS][0] /= NUM_LV_ESTIMATORS;
            estimates[NUM_LV_ESTIMATORS][1] /= NUM_LV_ESTIMATORS;
            estimates[NUM_LV_ESTIMATORS][2] /= NUM_LV_ESTIMATORS;
            
            for(int j = 0; j < NUM_LV_ESTIMATORS; ++j){
                double vDiff = estimates[j][0] - estimates[NUM_LV_ESTIMATORS][0];
                double aDiff = estimates[j][1] - estimates[NUM_LV_ESTIMATORS][1];
                double dDiff = estimates[j][2] - estimates[NUM_LV_ESTIMATORS][2];
                distribution[i] += (vDiff * vDiff) + (aDiff * aDiff) + (dDiff * dDiff);
            }
            normalFact += distribution[i];
        }
        
     /*   Collection ordersToTry = new LinkedHashSet();
        for(i = 0; i < SAMPLE_SIZE; ++i){
            double choice = random.nextDouble() * normalFact;
            double current = 0.;
            for(int j = 0; j < distribution.length; ++j) {
                current += distribution[j];
                if (current > choice) {
                    ordersToTry.add(orderArr[j]);
                    break;
                }
            }
        }
        return ordersToTry;*/
        return sample(orderArr, distribution, normalFact);
    }
    
    public static int SAMPLE_SIZE = 1;
    public Collection sample(Order [] orders, double [] distribution, double normalFact){
        Collection ordersToTry = new LinkedHashSet();
        for(int i = 0; i < SAMPLE_SIZE; ++i){
            double choice = random.nextDouble() * normalFact;
            double current = 0.;
            for(int j = 0; j < distribution.length; ++j) {
                current += distribution[j];
                if (current > choice) {
                    ordersToTry.add(orders[j]);
                    break;
                }
            }
        }
        return ordersToTry;
    }
  
    static void genOrders(OrderConstraintSet ocs, List allVars, Collection already, Collection never, Collection result) {
        if (out_t != null) out_t.println("Generating orders for "+allVars);
        List orders;
        int nOrders = ocs.approxNumOrders(allVars.size());
        if (nOrders > CANDIDATE_SET_SIZE*20) {
            if (out_t != null) out_t.println("Too many possible orders ("+nOrders+")!  Using random sampling.");
            orders = new LinkedList();
            for (int i = 0; i < CANDIDATE_SET_SIZE; ++i) {
                orders.add(ocs.generateRandomOrder(allVars));
            }
        } else {
            if (out_t != null) out_t.println("Estimated "+nOrders+" orders.");
            orders = ocs.generateAllOrders(allVars);
        }
        for (Iterator m = orders.iterator(); m.hasNext(); ) {
            Order best = (Order) m.next();
            if (never.contains(best)) {
                if (out_t != null) out_t.println("Skipped order "+best+" because it has blown up before.");
                continue;
            }
            if (already == null || !already.contains(best)) {
                if (out_t != null) out_t.println("Adding to candidate set: "+best);
                result.add(best);
                if (result.size() > CANDIDATE_SET_SIZE) {
                    if (out_t != null) out_t.println("Candidate set full.");
                    return;
                }
            } else {
                if (out_t != null) out_t.println("We have already tried order "+best);
            }
        }
    }
    
    static TrialGuess genGuess(Order best, double score,
            double vClass, double aClass, double dClass,
            Discretization vDis, Discretization aDis, Discretization dDis) {
        double vLowerBound, vUpperBound, aLowerBound, aUpperBound, dLowerBound, dUpperBound;
        vLowerBound = vUpperBound = aLowerBound = aUpperBound = dLowerBound = dUpperBound = -1;

        if (vDis != null && !Double.isNaN(vClass) && vClass != NO_CLASS) {
            vLowerBound = vDis.cutPoints == null || vClass <= 0 ? 0 : vDis.cutPoints[(int) vClass - 1];
            vUpperBound = vDis.cutPoints == null || vClass == vDis.cutPoints.length ? Double.MAX_VALUE : vDis.cutPoints[(int) vClass];
        }
        if (aDis != null && !Double.isNaN(aClass) && aClass != NO_CLASS) {
            aLowerBound = aDis.cutPoints == null || aClass <= 0 ? 0 : aDis.cutPoints[(int) aClass - 1];
            aUpperBound = aDis.cutPoints == null || aClass == aDis.cutPoints.length ? Double.MAX_VALUE : aDis.cutPoints[(int) aClass];
        }
        if (dDis != null && !Double.isNaN(dClass) && dClass != NO_CLASS) {
            dLowerBound = dDis.cutPoints == null || dClass <= 0 ? 0 : dDis.cutPoints[(int) dClass - 1];
            dUpperBound = dDis.cutPoints != null || dClass == dDis.cutPoints.length ? Double.MAX_VALUE : dDis.cutPoints[(int) dClass];
        }
        TrialPrediction prediction = new TrialPrediction(score, vLowerBound,vUpperBound,aLowerBound, aUpperBound,dLowerBound,dUpperBound);
        return new TrialGuess(best, prediction);
    }
    
    static TrialGuess genGuess(OrderConstraintSet ocs, double score, List allVars, double bestScore,
        double vClass, double aClass, double dClass,
        Discretization vDis, Discretization aDis, Discretization dDis,
        TrialCollection tc, Collection never) {
        if (out_t != null) out_t.println("Generating orders for "+allVars);
        // Choose a random one first.
        Order best = ocs.generateRandomOrder(allVars);
        Iterator m = Collections.singleton(best).iterator();
        boolean exhaustive = true;
        while (m.hasNext()) {
            best = (Order) m.next();
            if (never.contains(best)) {
                if (out_t != null) out_t.println("Skipped order "+best+" because it has blown up before.");
                continue;
            }
            if (tc == null || !tc.contains(best)) {
                if (out_t != null) out_t.println("Using order "+best);
                return genGuess(best, score, vClass, aClass, dClass, vDis, aDis, dDis);
            } else {
                if (out_t != null) out_t.println("We have already tried order "+best);
            }
            if (exhaustive) {
                List orders = ocs.generateAllOrders(allVars);
                m = orders.iterator();
                exhaustive = false;
            }
       }
        return null;
    }

    static Collection/*OrderConstraintSet*/ tryConstraints(
            MyId3 v, double vClass, Instances vData,
            MyId3 a, double aClass, Instances aData,
            MyId3 d, double dClass, Instances dData,
            MultiMap a2v, MultiMap d2v) {
        Collection results = new LinkedList();
        Collection vBestAttribs;
        if ((vClass >= 0 || Double.isNaN(vClass)) && v != null)
            vBestAttribs = v.getAttribCombos(vData.numAttributes(), vClass);
        else
            vBestAttribs = Collections.singleton(makeEmptyConstraint());
        if (vBestAttribs == null) return null;
        for (Iterator v_i = vBestAttribs.iterator(); v_i.hasNext(); ) {
            double[] v_c = (double[]) v_i.next();
            OrderConstraintSet ocs = new OrderConstraintSet();
            boolean v_r = constrainOrder(ocs, v_c, vData, null);
            if (!v_r) {
                continue;
            }
            if (out_t != null) out_t.println(" Order constraints (var="+(int)vClass+"): "+ocs);

            Collection aBestAttribs;
            if ((aClass >= 0 || Double.isNaN(aClass)) && a != null)
                aBestAttribs = a.getAttribCombos(aData.numAttributes(), aClass);
            else
                aBestAttribs = Collections.singleton(makeEmptyConstraint());
            if (aBestAttribs == null) continue;
            for (Iterator a_i = aBestAttribs.iterator(); a_i.hasNext(); ) {
                double[] a_c = (double[]) a_i.next();
                OrderConstraintSet ocsBackup = null;
                if (a_i.hasNext()) ocsBackup = ocs.copy();
                boolean a_r = constrainOrder(ocs, a_c, aData, a2v);
                if (!a_r) {
                    ocs = ocsBackup;
                    continue;
                }
                if (out_t != null) out_t.println("  Order constraints (attrib="+(int)aClass+"): "+ocs);

                Collection dBestAttribs;
                if ((dClass >= 0 || Double.isNaN(dClass)) && d != null)
                    dBestAttribs = d.getAttribCombos(dData.numAttributes(), dClass);
                else
                    dBestAttribs = Collections.singleton(makeEmptyConstraint());
                if (dBestAttribs != null) {
                    for (Iterator d_i = dBestAttribs.iterator(); d_i.hasNext(); ) {
                        double[] d_c = (double[]) d_i.next();
                        OrderConstraintSet ocsBackup2 = null;
                        if (d_i.hasNext()) ocsBackup2 = ocs.copy();
                        boolean d_r = constrainOrder(ocs, d_c, dData, d2v);
                        if (d_r) {
                            if (out_t != null) out_t.println("   Order constraints (domain="+(int)dClass+"): "+ocs);
                            results.add(ocs);
                        }
                        ocs = ocsBackup2;
                    }
                }
                ocs = ocsBackup;
            }
        }
        return results;
    }

    static double computeScore(int vC, int aC, int dC,
        double[] vMeans, double[] aMeans, double[] dMeans,
        double vWeight, double aWeight, double dWeight) {
        double score = vMeans[vC] * vWeight;
        score += aMeans[aC] * aWeight;
        score += dMeans[dC] * dWeight;
        return score;
    }

    static double[] makeEmptyConstraint() {
        int size = 0;
        double[] d = new double[size];
        for (int i = 0; i < d.length; ++i) {
            d[i] = Double.NaN;
        }
        return d;
    }
    
    static boolean constrainOrder(OrderConstraintSet ocs, double[] c, Instances data, MultiMap map) {
        for (int iii = 0; iii < c.length; ++iii) {
            if (Double.isNaN(c[iii])) continue;
            int k = (int) c[iii];
            OrderAttribute oa = (OrderAttribute) data.attribute(iii);
            OrderConstraint oc = oa.getConstraint(k);
            if (map != null) {
                Collection c1 = map.getValues(oc.getFirst());
                Collection c2 = map.getValues(oc.getSecond());
                boolean any = false;
                for (Iterator ii = c1.iterator(); ii.hasNext();) {
                    Object a = ii.next();
                    for (Iterator jj = c2.iterator(); jj.hasNext();) {
                        Object b = jj.next();
                        OrderConstraint cc = OrderConstraint.makeConstraint(oc.getType(), a, b);
                        boolean r = ocs.constrain(cc);
                        if (r) {
                            any = true;
                        }
                    }
                }
                if (!any) {
                    if (TRACE > 3) out.println("Constraint "+oc+" conflicts with "+ocs);
                    return false;
                }
            } else {
                boolean r = ocs.constrain(oc);
                if (!r) {
                    if (TRACE > 3) out.println("Constraint "+oc+" conflicts with "+ocs);
                    return false;
                }
            }
        }
        return true;
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
                Order o = ocs.generateRandomOrder(allVars);
                out.println("Good order: " + o);
            }
        }
    }

    TrialGuess evalOrder(Order o, InferenceRule ir) {
        List allVars = o.getFlattened();
        return tryNewGoodOrder(null, allVars, ir, o, false);
    }
    
    void printBestBDDOrders(StringBuffer sb, double score, Collection domains, OrderConstraintSet ocs,
            MultiMap rulesToTrials, List rules) {
        if (rules == null || rules.isEmpty()) {
            Collection orders;
            if (ocs.approxNumOrders(domains.size()) > 1000) {
                orders = new LinkedList();
                for (int i = 0; i < 5; ++i) {
                    orders.add(ocs.generateRandomOrder(domains));
                }
            } else {
                orders = ocs.generateAllOrders(domains);
            }
            for (Iterator j = orders.iterator(); j.hasNext(); ) {
                Order o = (Order) j.next();
                sb.append("Score "+format(score)+": "+o.toVarOrderString(null));
                sb.append('\n');
            }
            return;
        }
        if (!ocs.onlyOneOrder(domains.size())) {
            InferenceRule ir = (BDDInferenceRule) rules.get(0);
            List rest = rules.subList(1, rules.size());
            if (ir instanceof BDDInferenceRule && rulesToTrials.containsKey(ir)) {
                BDDInferenceRule bddir = (BDDInferenceRule) rules.get(0);
                OrderTranslator t = new MapBasedTranslator(bddir.variableToBDDDomain);
                TrialCollection tc = new TrialCollection("rule"+bddir.id, 0);
                for (int i = 0; i < 5; ++i) {
                    TrialGuess tg = tryNewGoodOrder(tc, new ArrayList(bddir.necessaryVariables), bddir, true);
                    if (tg == null) break;
                    OrderConstraintSet ocs2 = new OrderConstraintSet(ocs);
                    Order bddOrder = t.translate(tg.order);
                    boolean worked = ocs2.constrain(bddOrder);
                    double score2 = tg.prediction.score * (bddir.totalTime+1) / 1000;
                    if (worked) {
                        printBestBDDOrders(sb, score + score2, domains, ocs2, rulesToTrials, rest);
                    }
                    tc.addTrial(tg.order, null, 0);
                }
            } else {
                printBestBDDOrders(sb, score, domains, ocs, rulesToTrials, rest);
            }
        }
        Order o = ocs.generateRandomOrder(domains);
        for (Iterator k = rules.iterator(); k.hasNext(); ) {
            BDDInferenceRule ir = (BDDInferenceRule) k.next();
            Order o2;
            if (false) {
                MultiMap d2v = new GenericMultiMap();
                for (Iterator a = ir.variableToBDDDomain.entrySet().iterator(); a.hasNext(); ) {
                    Map.Entry e = (Map.Entry) a.next();
                    d2v.add(e.getValue(), e.getKey());
                }
                o2 = new MapBasedTranslator(d2v).translate(o);
            } else {
                Map d2v = new HashMap();
                for (Iterator a = ir.variableToBDDDomain.entrySet().iterator(); a.hasNext(); ) {
                    Map.Entry e = (Map.Entry) a.next();
                    d2v.put(e.getValue(), e.getKey());
                }
                o2 = new MapBasedTranslator(d2v).translate(o);
            }
            TrialGuess tg = tryNewGoodOrder(null, new ArrayList(ir.necessaryVariables), ir, o2, true);
            score += tg.prediction.score * (ir.totalTime+1) / 1000;
        }
        sb.append("Score "+format(score)+": "+o.toVarOrderString(null));
        sb.append('\n');
    }
    
    public void printBestBDDOrders() {
        MultiMap ruleToTrials = new GenericMultiMap();
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection tc = (TrialCollection) i.next();
            ruleToTrials.add(tc.getRule(solver), tc);
        }
        // Sort rules by their run time.
        SortedSet sortedRules = new TreeSet(new Comparator() {
            public int compare(Object o1, Object o2) {
                if (o1 == o2) return 0;
                if (o1 instanceof NumberingRule) return -1;
                if (o2 instanceof NumberingRule) return 1;
                BDDInferenceRule r1 = (BDDInferenceRule) o1;
                BDDInferenceRule r2 = (BDDInferenceRule) o2;
                long diff = r2.totalTime - r1.totalTime;
                if (diff != 0)
                    return (int) diff;
                return r1.id - r2.id;
            }
        });
        sortedRules.addAll(solver.getRules());
        ArrayList list = new ArrayList(sortedRules);
        Collection domains = new FlattenedCollection(solver.getBDDDomains().values());
        System.out.println("BDD Domains: "+domains);
        OrderConstraintSet ocs = new OrderConstraintSet();
        StringBuffer sb = new StringBuffer();
        printBestBDDOrders(sb, 0, domains, ocs, ruleToTrials, list);
        System.out.println(sb);
    }
    
    public void printBestTrials() {
        MultiMap ruleToTrials = new GenericMultiMap();
        for (Iterator i = allTrials.iterator(); i.hasNext(); ) {
            TrialCollection tc = (TrialCollection) i.next();
            ruleToTrials.add(tc.getRule(solver), tc);
        }
        // Sort rules by their run time.
        SortedSet sortedRules = new TreeSet(new Comparator() {
            public int compare(Object o1, Object o2) {
                if (o1 == o2) return 0;
                BDDInferenceRule r1 = (BDDInferenceRule) o1;
                BDDInferenceRule r2 = (BDDInferenceRule) o2;
                long diff = r2.totalTime - r1.totalTime;
                if (diff != 0)
                    return (int) diff;
                return r1.id - r2.id;
            }
        });
        sortedRules.addAll(ruleToTrials.keySet());
        
        for (Iterator i = sortedRules.iterator(); i.hasNext(); ) {
            BDDInferenceRule ir = (BDDInferenceRule) i.next();
            Map scoreboard = new HashMap();
            for (Iterator j = ruleToTrials.getValues(ir).iterator(); j.hasNext(); ) {
                TrialCollection tc = (TrialCollection) j.next();
                TrialInfo ti = tc.getMinimum();
                if (ti == null || ti.isMax()) continue;
                long[] score = (long[]) scoreboard.get(ti.order);
                if (score == null) scoreboard.put(ti.order, score = new long[2]);
                score[0]++;
                score[1] += ti.cost;
            }
            
            if (scoreboard.isEmpty()) continue;
            
            SortedSet sortedTrials = new TreeSet(new Comparator() {
                public int compare(Object o1, Object o2) {
                    long[] counts1 = (long[]) ((Map.Entry) o1).getValue();
                    long[] counts2 = (long[]) ((Map.Entry) o2).getValue();
                    long diff = counts2[0] - counts1[0];
                    if (diff != 0)
                        return (int) diff;
                    diff = counts2[1] - counts1[1];
                    if (diff != 0)
                        return (int) diff;
                    Order order1 = (Order) ((Map.Entry) o1).getKey();
                    Order order2 = (Order) ((Map.Entry) o2).getKey();
                    return order1.compareTo(order2);
                }
            });
            sortedTrials.addAll(scoreboard.entrySet());
            
            out.println("For rule"+ir.id+": "+ir);
            for (Iterator it = sortedTrials.iterator(); it.hasNext();) {
                Map.Entry entry = (Map.Entry) it.next();
                Order order = (Order) entry.getKey();
                long[] counts = (long[]) entry.getValue();
                double aveTime = (double)counts[1] / (double) counts[0];
                String bddString = order.toVarOrderString(ir.variableToBDDDomain);
                out.println(order + " won " + counts[0] + " time(s), average winning time of "+format(aveTime)+" ms");
                out.println("   BDD order: "+bddString);
            }
            out.println();
        }
        
    }
    
    public void printTrialsDistro() {
        printTrialsDistro(allTrials, solver);
    }

    public static void printTrialsDistro(Collection trials, Solver solver) {
        Map orderToCounts = new HashMap();
        final int numRules = solver.getRules().size();
        int total = 0, distinct = 0;
        for (Iterator it = trials.iterator(); it.hasNext();) {
            TrialCollection tc = (TrialCollection) it.next();
            Assert._assert(tc != null);
            for (Iterator jt = tc.getTrials().iterator(); jt.hasNext();) {
                TrialInfo ti = (TrialInfo) jt.next();
                Order order = ti.order;
                int[] counts = (int[]) orderToCounts.get(order);
                if (counts == null) {
                    counts = new int[numRules + 1];
                    orderToCounts.put(order, counts);
                    ++distinct;
                }
                ++counts[tc.getRule(solver).id];
                //one extra int at the end to count the total number of trials
                ++counts[numRules];
            }
            total += tc.size();
        }

        SortedSet sortedTrials = new TreeSet(new Comparator() {
            public int compare(Object o1, Object o2) {
                int[] counts1 = (int[]) ((Map.Entry) o1).getValue();
                int[] counts2 = (int[]) ((Map.Entry) o2).getValue();
                int diff = counts2[numRules] - counts1[numRules];
                if (diff != 0)
                    return diff;
                Order order1 = (Order) ((Map.Entry) o1).getKey();
                Order order2 = (Order) ((Map.Entry) o2).getKey();
                return order1.compareTo(order2);
            }
        });

        sortedTrials.addAll(orderToCounts.entrySet());
        out.println(total + " trials  of " + distinct + " distinct orders");
        out.println("tried Orders: ");
        for (Iterator it = sortedTrials.iterator(); it.hasNext();) {
            Map.Entry entry = (Map.Entry) it.next();
            Order order = (Order) entry.getKey();
            int[] counts = (int[]) entry.getValue();
            out.println(order + " tried a total of " + counts[numRules] + " time(s) :");
            for (int i = 0; i < counts.length - 1; ++i) {
                int count = counts[i];
                if (count != 0) {
                    out.println("    " + count + " time(s) on \n    " + solver.getRule(i));
                }
            }
            out.println();
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

        FindBestDomainOrder dis = ((BDDSolver) s).fbo;
        //dis.loadTrials("trials.xml");
        //dis.dump();

        for (Iterator i = s.rules.iterator(); i.hasNext();) {
            InferenceRule ir = (InferenceRule) i.next();
            if (ir.necessaryVariables == null) continue;
            System.out.println("Computing for rule " + ir);

            List allVars = new LinkedList();
            allVars.addAll(ir.necessaryVariables);
            System.out.println("Variables = " + allVars);

            TrialGuess guess = dis.tryNewGoodOrder(null, allVars, ir, false);

            System.out.println("Resulting guess: "+guess);
        }

        printTrialsDistro(dis.allTrials, s);
        dis.printBestTrials();
        dis.printBestBDDOrders();
    }
    
}
