/*
 * Created on Jan 15, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package net.sf.bddbddb.order;

import java.util.Iterator;

import net.sf.bddbddb.BDDInferenceRule;
import net.sf.bddbddb.FindBestDomainOrder;
import net.sf.bddbddb.order.WekaInterface.OrderAttribute;
import net.sf.bddbddb.order.WekaInterface.OrderInstance;
import weka.core.Instance;
import weka.core.Instances;


public class TrialInstance extends OrderInstance implements Comparable {

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

    public TrialInfo ti;

    public TrialInstance(double weight, double[] d, Order o, TrialInfo ti) {
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
        return FindBestDomainOrder.compare(this.getCost(), that.getCost());
    }

    public boolean isMaxTime() {
        return ti.cost >= BDDInferenceRule.LONG_TIME;
    }
    
    public static TrialInstance cloneInstance(TrialInstance instance){
        return new TrialInstance(instance.weight(), instance.toDoubleArray(), instance.getOrder(), instance.getTrialInfo());
    }

}