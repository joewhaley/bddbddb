/*
 * Created on Jan 15, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package net.sf.bddbddb.order;

import java.util.Arrays;
import java.util.Collection;
import java.util.Date;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import net.sf.bddbddb.BDDInferenceRule;
import net.sf.bddbddb.FindBestDomainOrder;
import net.sf.bddbddb.InferenceRule;
import net.sf.bddbddb.Solver;

import org.jdom.Element;


/**
 * A collection of trials on the same test. (The same BDD operation.)
 * 
 * @author John Whaley
 * @version $Id$
 */
public class TrialCollection {
    /**
     * Name of the test.
     */
    public String name;

    /**
     * Time of the test.
     */
    long timeStamp;
    
    public static String RULE_CONST = "rule";
    public static String SPACER = "_";
    public static String UPDATE_CONST = "update";
    /**
     * Map from orders to their trial information.
     */
    public Map/*<Order,TrialInfo>*/ trials;

    /**
     * Best trial so far.
     */
    TrialInfo best;

    /**
     * Trial info sorted by cost. Updated automatically when necessary.
     */
    transient TrialInfo[] sorted;

    /**
     * Construct a new collection of trials.
     * 
     * @param n  test name
     */
    public TrialCollection(BDDInferenceRule rule, long ts) {
        name = RULE_CONST + rule.id + SPACER + UPDATE_CONST + rule.updateCount;     
        timeStamp = ts;
        trials = new LinkedHashMap();
        sorted = null;
    }

    TrialCollection(String n, long ts){
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
        if (FindBestDomainOrder.TRACE > 2) FindBestDomainOrder.out.println(this+": Adding trial "+i);
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
        return name + "@" + FindBestDomainOrder.dateFormat.format(new Date(timeStamp));
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
        int spacerIndex = s.indexOf(SPACER);
        int ruleNum = -1;
        if(spacerIndex > -1)
            ruleNum = Integer.parseInt(s.substring(RULE_CONST.length(),spacerIndex));
        else
            ruleNum = Integer.parseInt(s.substring(RULE_CONST.length()));
        
        InferenceRule rule = solver.getRule(ruleNum);
        return rule;
    }
    
    static int parseUpdateCount(String s){
       int spacerIndex = s.indexOf(SPACER);
       if(spacerIndex > -1)
           return Integer.parseInt(s.substring(spacerIndex + 1 + UPDATE_CONST.length()));
    
        return spacerIndex;
    }

    public InferenceRule getRule(Solver solver) {
        return parseRule(solver, name);
    }
    
    public int getUpdateCount(){ return parseUpdateCount(name); }

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