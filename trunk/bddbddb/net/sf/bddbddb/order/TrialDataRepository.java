/*
 * Created on Jan 18, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package net.sf.bddbddb.order;

import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jwutil.collections.GenericMultiMap;
import jwutil.collections.MultiMap;
import jwutil.util.Assert;
import net.sf.bddbddb.BDDSolver;
import net.sf.bddbddb.FindBestDomainOrder;
import net.sf.bddbddb.InferenceRule;
import weka.classifiers.Classifier;
import weka.core.FastVector;
import weka.core.Instances;

/**
 * @author Administrator
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class TrialDataRepository {
    
    Collection allTrials;
    static int TRACE = FindBestDomainOrder.TRACE;
    Map /*InferenceRule, TrialDataGroup*/ varDataMap, /*Set, TrialDataGroup */attribDataMap, domainDataMap;
    MultiMap varListeners, attribListeners, domainListeners;
    static PrintStream out = FindBestDomainOrder.out;
    BDDSolver solver;
    public TrialDataRepository(BDDSolver solver){
        this.solver = solver;
        varDataMap = new HashMap();
        varListeners = new GenericMultiMap();
        attribDataMap = new HashMap();
        attribListeners = new GenericMultiMap();
        domainDataMap = new HashMap();
        domainListeners = new GenericMultiMap();
        allTrials = new LinkedList();
    }
    
    public TrialDataRepository(Collection allTrials, BDDSolver solver){
        this(solver);
        this.allTrials = allTrials;
    }
    
    public TrialInstances buildVarInstances(InferenceRule ir, List allVars) {
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
    
    public TrialInstances buildAttribInstances(InferenceRule ir, List allVars) {
        Collection allAttribs = VarToAttribMap.convert(allVars, ir);
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
    
    public TrialInstances buildDomainInstances(InferenceRule ir, List allVars) {
        Collection allDomains = AttribToDomainMap.convert(VarToAttribMap.convert(allVars, ir));
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
    
    public static void addToInstances(TrialInstances data, TrialCollection tc, OrderTranslator t) {
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
    

 
    public TrialDataGroup getVariableDataGroup(InferenceRule rule, List variables){
        TrialDataGroup dataGroup = (TrialDataGroup) varDataMap.get(variables);
        if(dataGroup == null){
            dataGroup = new TrialDataGroup.VariableTrialDataGroup(variables, buildVarInstances(rule, variables));
            varDataMap.put(variables, dataGroup);
            Collection pairs = WekaInterface.generateAllPairs(variables);
            for(Iterator it = pairs.iterator(); it.hasNext(); ){
                varListeners.add(it.next(), dataGroup); 
            }
        }
        return dataGroup;
    }
    
   
    public TrialDataGroup getAttribDataGroup(InferenceRule rule, List variables){
        Set attribs = new HashSet(VarToAttribMap.convert(variables, rule));
        TrialDataGroup dataGroup = (TrialDataGroup) attribDataMap.get(attribs);
        if(dataGroup == null){
            dataGroup = new TrialDataGroup.AttribTrialDataGroup(attribs, buildAttribInstances(rule, variables));
            attribDataMap.put(attribs, dataGroup);
            Collection pairs = WekaInterface.generateAllPairs(attribs);
            for(Iterator it = pairs.iterator(); it.hasNext(); ){
                attribListeners.add(it.next(), dataGroup); 
            }
        }
        return dataGroup;
    }
    
    public TrialDataGroup getDomainDataGroup(InferenceRule rule, List variables){
        List domains = new LinkedList(AttribToDomainMap.convert(VarToAttribMap.convert(variables, rule)));
        Set domainSet = new HashSet(domains);
        TrialDataGroup dataGroup = (TrialDataGroup) domainDataMap.get(domainSet);
        if(dataGroup == null){
            dataGroup = new TrialDataGroup.DomainTrialDataGroup(domains, buildDomainInstances(rule, variables) );
            domainDataMap.put(domainSet, dataGroup);
            Collection pairs = WekaInterface.generateAllPairs(domains);
            for(Iterator it = pairs.iterator(); it.hasNext(); ){
                domainListeners.add(it.next(), dataGroup); 
            }
        }
        return dataGroup;
    }
    
    public boolean addTrial(InferenceRule rule, List variables, TrialInfo info){
        Order o_v = info.order;
        TrialCollection tc = info.getCollection();
        double trialColBest;
        if (tc.getMinimum().isMax()) trialColBest = 1;
        else trialColBest = (double) tc.getMinimum().cost + 1;
        
        //boolean changed = varData.update(o_v,info, trialColBest);
        boolean changed = false;
        Collection varPairs = WekaInterface.generateAllPairs(variables);
        Collection notified = new HashSet();
        for(Iterator it = varPairs.iterator(); it.hasNext(); ){
            Collection listeners = varListeners.getValues(it.next());                                              
            Assert._assert(listeners != null);
            for(Iterator jt = listeners.iterator(); jt.hasNext();){
                TrialDataGroup dataGroup = (TrialDataGroup) jt.next();
                if(!notified.contains(dataGroup)){
                    changed |= dataGroup.update(o_v, info,trialColBest);
                    notified.add(dataGroup);
                }
            }
        }
        
        OrderTranslator translator = new VarToAttribTranslator(rule);
        Order o_a = translator.translate(o_v);
        Collection attribs = VarToAttribMap.convert(variables, rule);
        Collection attribPairs = WekaInterface.generateAllPairs(attribs);
        for(Iterator it = attribPairs.iterator(); it.hasNext(); ){
            Collection listeners = attribListeners.getValues(it.next());                                              
            Assert._assert(listeners != null);
            for(Iterator jt = listeners.iterator(); jt.hasNext();){
                TrialDataGroup dataGroup = (TrialDataGroup) jt.next();
                if(!notified.contains(dataGroup)){
                    changed |= dataGroup.update(o_a, info,trialColBest);
                    notified.add(dataGroup);
                }
            }
        }
        Order o_d = AttribToDomainTranslator.INSTANCE.translate(o_a);
        Collection domainPairs = WekaInterface.generateAllPairs(AttribToDomainMap.convert(attribs));
        for(Iterator it = domainPairs.iterator(); it.hasNext(); ){
            Collection domListeners = domainListeners.getValues(it.next());
            Assert._assert(domListeners != null);
            for(Iterator jt = domListeners.iterator(); jt.hasNext(); ){
                TrialDataGroup dataGroup = (TrialDataGroup) jt.next();
                if(!notified.contains(dataGroup)){
                    changed |= dataGroup.update(o_d, info, trialColBest);
                    notified.add(dataGroup);
                }
            }
        }
       
        return changed;
    }
    public abstract static class TrialDataGroup{

        public static String CLASSIFIER = "net.sf.bddbddb.order.MyId3";
        private TrialInstances trialInstances;
        private TrialInstances trialInstancesCopy;
        private Discretization discretization;
        private double discretizeParam = 0;
        private double thresholdParam = 0;
        
        private Classifier classifier;
        private double infoSinceClassRebuild, infoSinceDiscRebuild, infoSinceInstances;
        private double infoThreshold; 
        protected FilterTranslator filter;
        protected TrialDataGroup(TrialInstances instances){
            trialInstances = instances;
            discretizeParam  = -1;
            thresholdParam = -1;
        }
        
        /**
         * @return Returns the classifier.
         */
        public Classifier classify() {
            if(discretizeParam < 0 && thresholdParam < 0)
                return null;
            Assert._assert(discretizeParam < 0 ^ thresholdParam < 0); //kinda weird
           
           if(discretizeParam > 0)
               discretize(discretizeParam);
           else
               threshold(thresholdParam);
          TrialInstances instances = getTrialInstances();
            classifier = instances.numInstances() > 0 ? WekaInterface.buildClassifier(CLASSIFIER, instances) : null;
            return classifier;
        }
        
        public void setDiscretizeParam(double discretize){
            discretizeParam = discretize;
            thresholdParam = -1;
        }
        
        public void setThresholdParam(double thresholdParam){
            this.thresholdParam = thresholdParam;
            discretizeParam = -1;
        }
        /**
         * @return Returns the discretization.
         */
        public Discretization discretize(double discretizeFact) {
            if((discretizeFact != discretizeParam) || (infoSinceDiscRebuild > infoThreshold)){
                setDiscretizeParam(discretizeFact);
                discretization = getTrialInstances().discretize(discretizeParam);
                infoSinceDiscRebuild = 0;
            }
            return discretization;
        }
       
        public Discretization threshold(double threshold){
            if((threshold != thresholdParam) || (infoSinceDiscRebuild > infoThreshold)){
                setThresholdParam(threshold);
                discretization = getTrialInstances().threshold(thresholdParam);
                infoSinceDiscRebuild = 0;
            }
            return discretization;
        }
        
        /**
         * @return Returns the instances.
         */
        public TrialInstances getTrialInstances() {
            if(trialInstancesCopy == null || infoSinceInstances > infoThreshold){
                trialInstancesCopy = trialInstances.copy();
                infoSinceInstances = 0;
            }
            return trialInstancesCopy;
        }
        
        public boolean update(Order order, TrialInfo info, double trialColBest){
            infoSinceClassRebuild = Double.POSITIVE_INFINITY;
            infoSinceDiscRebuild = Double.POSITIVE_INFINITY;
            infoSinceInstances = Double.POSITIVE_INFINITY;
            Order filteredOrder = filter.translate(order);
            Assert._assert(filteredOrder.numberOfElements() > 1);
            System.out.println("Order: " + order + "\n" + filter + "\nfiltered order: " + filteredOrder);
            double score = (double) (info.cost + 1) / trialColBest; 
            TrialInstance instance = TrialInstance.construct(info, filteredOrder, score, trialInstances);
            if(instance == null){
                System.out.println("Failed constructing instance of " + filteredOrder + " with " + filter + " on " + trialInstances);
                Assert.UNREACHABLE();
            }
            System.out.println("Adding new Instance to DataGroup: " + this);
            trialInstances.add(instance);
            return true;
        }
        
        public static class VariableTrialDataGroup extends TrialDataGroup{
            private Collection variables;
            public VariableTrialDataGroup(Collection variables, TrialInstances instances){
                super(instances);
                this.variables = variables;
                this.filter = new FilterTranslator(variables);
            }
          
            public Collection getVariables(){ return new LinkedList(variables); }
        }
        
        public static class AttribTrialDataGroup extends TrialDataGroup{
            private Collection attribs;
            public AttribTrialDataGroup(Collection attribs, TrialInstances instances){
               super(instances);
               this.attribs = attribs;
               this.filter = new FilterTranslator(attribs);
            }
        }
        
        public static class DomainTrialDataGroup extends TrialDataGroup{
            private Collection domains;
            public DomainTrialDataGroup(Collection domains, TrialInstances instances){
                super(instances);
                this.domains = domains;
                this.filter = new FilterTranslator(domains);
            }
        }
        
    }
}