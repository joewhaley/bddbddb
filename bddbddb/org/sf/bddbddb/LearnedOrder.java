// LearnedOrder.java, created Jul 27, 2004 8:57:36 PM 2004 by mcarbin
// Copyright (C) 2004 Michael Carbin <mcarbin@stanford.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.StringTokenizer;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Result;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import jwutil.collections.IndexMap;
import jwutil.collections.Pair;
import jwutil.math.PermutationGenerator;
import jwutil.util.Assert;
import org.sf.bddbddb.OrderClassifier.MyAttribute;
import org.sf.bddbddb.OrderClassifier.MyInstance;
import org.sf.bddbddb.dataflow.PartialOrder.BeforeConstraint;
import org.sf.bddbddb.dataflow.PartialOrder.Constraint;
import org.sf.bddbddb.dataflow.PartialOrder.Constraints;
import org.sf.bddbddb.dataflow.PartialOrder.InterleavedConstraint;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;
import org.sf.javabdd.JFactory;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xml.sax.SAXException;

/**
 * LearnedOrder
 * 
 * @author mcarbin
 * @version $Id$
 */
public class LearnedOrder {
    String bestOrder;
    String origOrder;
    long bestTime;
    OrderClassifier classifier;
    BDDInferenceRule rule;
    List domainSet;
    int nodeTableSize, cacheSize, maxIncrease;
    int id;
    RoundedOrderGenerator gen;
    boolean isTrained;
    static boolean TRACE = true;
    static Random randomNumGen;
    long DELAY = 0;
    
    long MAX_WAIT_TIME = 70000;
    int MAX_PERMUTATIONS = Integer.MAX_VALUE;
    int SIZE_OF_TRAINING_SET = 10;
    int ROUND_SIZE = 10;
    double MIN_CONFIDENCE = .04;
    
    static IndexMap ruleIDs;
    static String learnDir;
    static String ruleIDsFilename;
    static boolean idsLoaded = false;
    static{
        randomNumGen = new Random(System.currentTimeMillis());
        
    }
   
    
    int startIteration = 0;
    Document stats = null;
    public File[][] bddsToLoad;
    
    public LearnedOrder(BDDInferenceRule rule){
        this.rule = rule;
        this.bestTime = Long.MAX_VALUE;
        this.origOrder = rule.solver.VARORDER;
        isTrained = false;
        domainSet = new LinkedList();
    }
    
    public void initialize(){
        
        Set domains = new HashSet();
        
        for(Iterator it = rule.top.iterator(); it.hasNext(); ){
            BDDRelation r = (BDDRelation) ((RuleTerm) it.next()).getRelation();
            domains.addAll(r.getBDDDomains());
        }
        domainSet.addAll(domains);
        classifier = new OrderClassifier(rule,domainSet, MAX_WAIT_TIME);
        
        System.out.println("rule string: " + rule.toString());
        
        loadRuleIDs();
        if(ruleIDs.contains(rule.toString())){
            id = ruleIDs.get(rule.toString());
            
            if(load(learnDir + "rule" + id + ".classifier")){
                isTrained = true;
            }
        }else{
            id = ruleIDs.get(rule.toString());
            saveRuleIDs();
        }
        if(gen == null)
            gen = new TrainingOrderGenerator(domainSet, origOrder);
    }
    
    
    /* Learning Routines */
    
    public void learn(){
        
            if(bddsToLoad == null){
                System.out.println("Initial Bdds were never save. Can't use this method");
                return;
            }
            if(bddsToLoad[0].length <= 1) return; //skip trivial copy rules
            bddFilesAssert();
            
            learnWithSavedBDDs(bddsToLoad);
            deleteBDDs(bddsToLoad);
        }
    public static boolean skip = false;
    public void learn(BDD[] relationValues, BDD[] canQuantifyAfter, long time){ 
        if(skip) return;
        if(rule.updateCount != startIteration) return;
        if(relationValues.length > 1){     
            
            File[][] bddFiles = new File[2][];
            bddFiles[0] = saveBDDs(relationValues,"bdd");
            bddFiles[1] = saveBDDs(canQuantifyAfter,"quantbdd");
            
            learnWithSavedBDDs(bddFiles);
            deleteBDDs(bddFiles);
        }
    }
    
    public void learn(BDD[] relationValues, BDD[] rallRelationValues, BDD[] canQuantifyAfter){
        if(skip) return;
        if(rule.updateCount != startIteration) return; 
        
        if(relationValues.length > 1){
            
            File[][] bddFiles = new File[3][];
            bddFiles[0] = saveBDDs(relationValues,"bdd");
            bddFiles[1] = saveBDDs(rallRelationValues,"rallbdd");
            bddFiles[2] = saveBDDs(canQuantifyAfter,"quantbdd");
            
            learnWithSavedBDDs(bddFiles);
            
            deleteBDDs(bddFiles);
        }
    }
    
    public void learnWithSavedBDDs(File[][] bddFiles){
        
        File bddConfig = saveBDDConfig();
        int iteration = 0;  
        while(true){
            gen.resetRoundCounter();
            int i = -1;
            boolean changed = false;
            while(gen.hasNext()){
                ++i;
                
                String tryOrder = gen.nextOrder();
                System.out.println("Next order: " + tryOrder);
                if(isTrained){
                    String rating = classifier.classify(tryOrder);
                    if(!OrderClassifier.goodClusters.contains(rating)){
                        System.out.println("Order classified as bad: skipping");
                        continue;
                    }
                    
                    System.out.println("Order classified as good: trying");
                    
                }
                changed = true;
                tryOrder(tryOrder, gen.lastOrder, bddConfig, bddFiles, iteration,i);
            }
            
            ++iteration;
            try{
                System.out.println("Best Variable order: " + bestOrder);
                System.out.println("Best time: " + bestTime);
                
                if(changed){
                    classifier.buildClassifier();
                    // System.out.println(classifier);
                    
                    save();
                    writeStats();
                    gen.resetSeenOrders();
                }
            }catch(Exception e){         
                e.printStackTrace();
                Assert.UNREACHABLE("Could not build classifier");
            }
            if(!gen.existsMoreOrders()){
                if(!isTrained){
                    gen = new LearnedOrderGenerator(domainSet,origOrder, gen.triedOrders);
                    isTrained = true;
                }else
                    break;
            }
        } 
    }
   

    public void tryOrder(String tryOrder, List listTryOrder, File bddConfig, File[][] bddFiles, int iteration, int i){
        gen.addTriedOrder(listTryOrder);
        
        long waitTime = classifier.medianTime() + DELAY;
        System.out.println("Waiting for " + waitTime + " ms");
        TryThread t = new TryThread(tryOrder,bddConfig.getAbsolutePath(),bddFiles);
        t.start();
        try{
            
            t.join(waitTime);
        }catch(InterruptedException e){}
        t.stop();
        
        System.out.println("\nTook " + t.time + " milliseconds");
        
        if(t.time < bestTime){
            bestTime = t.time;
            bestOrder = tryOrder;
        }
        
        classifier.addOrder(tryOrder, t.time);
        addStat(tryOrder, iteration + ((double) i / ROUND_SIZE),  t.time, Math.min(waitTime,t.time));
        
    }

   
   
    /*IO Routines */
    /**
     * @param string
     */
    private boolean load(String string) {
        File file = new File(string);
        if(!file.exists()) return false;
     //   System.out.println("file: " + string);
        BufferedReader in = null;
        boolean loaded = false;
        try{
            in = new BufferedReader(new FileReader(file));
            bestOrder = in.readLine();
            bestTime = Long.parseLong(in.readLine());
            int numOrdersTried = Integer.parseInt(in.readLine());
            System.out.println("num orders: " + numOrdersTried);
            Set triedOrders = new HashSet();
            while(triedOrders.size() < numOrdersTried){
                String line = in.readLine();
              //  System.out.println("line: " + line);
                List order = parseOrder(line,rule.solver);
             //   System.out.println("order: " + order);
              //  if(triedOrders.contains(order)) System.out.println("dupe!!!");
                triedOrders.add(order);
             //   System.out.println("size: " + triedOrders.size());
            }
            this.gen = new LearnedOrderGenerator(domainSet,origOrder,triedOrders);
            classifier.load(in);
            return true;
        }catch(IOException e){
            e.printStackTrace();
        } finally {
            if (in != null) try {
                in.close();
            } catch (IOException _) {
            }
            
        }  
        return false;
    }
    
   
    private void loadRuleIDs(){
        if(idsLoaded) return;
        
        String basedir = rule.solver.basedir == null ? "" : rule.solver.basedir;
        learnDir =  basedir + File.separator 
        + "learning"  + File.separator; 
        
        ruleIDsFilename = learnDir + "ruleIDs.map";
        
        ruleIDs = new IndexMap("rule ids");
        File dir = new File(learnDir);
        
        if(!dir.exists()) dir.mkdir();
        
        File mapFile = new File(ruleIDsFilename);
        if(mapFile.exists()){ 
            try{
                ruleIDs = IndexMap.loadStringMap("rule ids", new BufferedReader(new FileReader(mapFile)));
                if(TRACE) System.out.println("Loaded rule ids file");
            }catch(IOException e){
                e.printStackTrace();
                Assert.UNREACHABLE("Could not load rule id map");
            }
        }else{
            ruleIDs = new IndexMap("rule ids");
        }
        idsLoaded = true;
    }
    private BDD[] loadBDDs(BDDFactory factory, File[] bddFiles){
        BDD[] bdds = new BDD[bddFiles.length];
        try{
            for(int i = 0; i < bdds.length; i++){
                if(bddFiles[i] == null) continue;
                bdds[i] = factory.load(bddFiles[i].getAbsolutePath());
            }
        }catch(IOException e){
            e.printStackTrace();
            Assert.UNREACHABLE("Loading bdds failed");
        }
        return bdds;
    }
    public File[] saveBDDs(BDD[] bdds, String name){
        File[] files = new File[bdds.length];
        try{
            
            for(int i = 0; i < bdds.length; i++){
                if(bdds[i] == null) continue;
                files[i] = File.createTempFile(name, Integer.toString(i));
                files[i].deleteOnExit();
                rule.solver.bdd.save(files[i].getAbsolutePath(),bdds[i]);
                
            }
        }catch(IOException e){
            e.printStackTrace();
            Assert.UNREACHABLE("Could not save bdds");
        }
        return files;
    }
    

    private void saveRuleIDs(){
        BufferedWriter out = null;
        try{
            out = new BufferedWriter(new FileWriter(ruleIDsFilename));
            ruleIDs.dumpStrings(out);
        }catch(IOException e){
            e.printStackTrace();
            Assert.UNREACHABLE("Could not save rule id map");
        } finally {
            if (out != null) try {
                out.close();
            } catch (IOException x) {
            }
        }
    }
    
    
    public void saveBddsToLoad(BDD[] oldRelationValues, BDD[] canQuantifyAfter){
        if(bddsToLoad != null){
            deleteBDDs(bddsToLoad);
        }
        
        bddsToLoad = new File[2][];
        bddsToLoad[0] = saveBDDs(oldRelationValues, "_rule" + id + ".vloadbdd");
        bddsToLoad[1] = saveBDDs(canQuantifyAfter, "_rule" + id + ".cloadbdd");
        
    }
    
    public void saveBddsToLoad(BDD[] oldRelationValues, BDD[] rallRelationValues, BDD[] canQuantifyAfter){
        if(bddsToLoad != null){
            deleteBDDs(bddsToLoad);
        }
        
        bddsToLoad = new File[3][]; 
        bddsToLoad[0] = saveBDDs(oldRelationValues, "_rule" + id + ".vloadbdd");
        bddsToLoad[1] = saveBDDs(rallRelationValues, "_rule" + id + ".rloadbdd");
        bddsToLoad[2] = saveBDDs(canQuantifyAfter, "_rule" + id + ".cloadbdd");
        
    }
   
    private void save(){    
        BufferedWriter out = null;
        try{
            out = new BufferedWriter(new FileWriter(learnDir + "rule" + id + ".classifier"));
            out.write(bestOrder + "\n");
            out.write(bestTime + "\n");
            out.write(gen.triedOrders.size() + "\n");
            for(Iterator it = gen.triedOrders.iterator(); it.hasNext(); ){
                out.write(orderListToString((List) it.next()) + "\n");
            }
            classifier.save(out);
        }catch(IOException e){
            e.printStackTrace();
            Assert.UNREACHABLE("Could not save learned information;");
        }finally {
            if (out != null) try {
                out.close();
            } catch (IOException x) {
            }
        }
    }

    
    public File saveBDDConfig(){
        File bddConfig = null;
        try{
            bddConfig = File.createTempFile("bddconfig","cfg");
            BDDFactoryUtils.writeBDDConfig(rule.solver.bdd,bddConfig.getAbsolutePath());
        }catch(IOException e){
            e.printStackTrace();
            Assert.UNREACHABLE("Writing bddconfig failed");
        }
        return bddConfig;
    }
    
    public void bddFilesAssert(){
        for(int i = 0; i < bddsToLoad.length; ++i){
            File[] files = bddsToLoad[i];
            for(int j = 0; j < files.length; ++j){
                if(files[j] != null)
                    Assert._assert(files[j].exists());
            }
        }
    }
    public static void deleteBDDs(File[][] bddFiles){
        for(int i = 0; i < bddFiles.length; ++i)
            deleteBDDs(bddFiles[i]);
    }
    
    public static void deleteBDDs(File[] bdds){
        for(int i = 0; i < bdds.length; i++){
            if(bdds[i] == null) continue;
            bdds[i].delete();
        }
    }
    
    private void writeStats(){    
        if(stats == null) return;
        
        try {
            File file = new File(learnDir + "rule" + id + "_stats.xml");
            // trick: cast Down to XmlDocument
            Source source = new DOMSource(stats);
            Result result = new StreamResult(file); 
            Transformer xformer = TransformerFactory.newInstance().newTransformer();
            xformer.transform(source,result);
        } catch (TransformerConfigurationException e) {
            e.printStackTrace();
        } catch (TransformerFactoryConfigurationError e) {
            e.printStackTrace();
        } catch (TransformerException e) {
            e.printStackTrace();
        }

    }

    public final static String ORDERS = "Orders";
    public final static String ORDER = "Order";
    public final static String ITERATION = "Iteration";
    public final static String SCORE = "Score";
    public final static String WAITTIME = "WaitTime";
    public void addStat(String order, double iteration, long score, long waitTime){
        if(stats == null) initStats();
        Element orderStat = stats.createElement(ORDERS);
        orderStat.setAttribute(ORDER, order);
        orderStat.setAttribute(ITERATION, Double.toString(iteration));
        orderStat.setAttribute(SCORE, Long.toString(score));
        orderStat.setAttribute(WAITTIME, Long.toString(waitTime));
        stats.getFirstChild().appendChild(orderStat);
        
    }
    
    public void initStats(){
        File file = new File(learnDir + "rule" + id + "_stats.xml");
        if(file.exists())
            stats = loadStatsXMLDoc(file);
        else
            stats = createStatsXMLDoc();
    }
    public Document createStatsXMLDoc(){
        DocumentBuilder db = createDocumentBuilder();
        Document doc  = db.newDocument();
        Element root = doc.createElement("rule" + id +"_statistics");
        doc.appendChild(root);
        
        return doc;
    }
    
    public Document loadStatsXMLDoc(File file){
        DocumentBuilder db = createDocumentBuilder();
        Document doc = null;
        try {
            doc = db.parse(file);
        } catch (SAXException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
        
        return doc;
    }
    
    public DocumentBuilder createDocumentBuilder(){
        // The following is the standard incantation to get a Document object
        // (i.e. I copied this from the API docs)
        DocumentBuilderFactory dbf =
            DocumentBuilderFactory.newInstance();
        
        dbf.setValidating(false);
        
        DocumentBuilder db = null;
        try {
            db = dbf.newDocumentBuilder();
        } catch (ParserConfigurationException pce) {
            pce.printStackTrace();
        }
        
        return db;
    }

    public void saveConstraints(){
        BufferedWriter out = null;
        try{
            out = new BufferedWriter(new FileWriter(learnDir + "rule" + id + ".cons", false));
            Constraints cons = getConstraints();
            for(Iterator it = cons.getAllConstraints().iterator(); it.hasNext(); )
                out.write(it.next() + "\n");
        }catch(IOException e){
            e.printStackTrace();
            Assert.UNREACHABLE("Could not save rule id map");
        } finally {
            if (out != null) try {
                out.close();
            } catch (IOException x) {
            }
        }
    }

/* Constraint Generation */
    public Constraints getConstraints(){
        System.out.println(rule);
        System.out.println("stats: ");

        Pair[] attrs = new Pair[classifier.getNumAttributes()];
        
        for(int i = 0; i < classifier.getNumAttributes(); ++i){
            weka.core.Attribute attr = ( weka.core.Attribute ) classifier.getAttributes().elementAt(i);
            
            //System.out.println(attr + ": ");
            double before = classifier.importance(attr,"<");
            
            before = Double.isNaN(before) ? 0 : before;
        //    System.out.println("importance <: " +  before);
            double inter = classifier.importance(attr,"=");
            inter = Double.isNaN(inter) ? 0 : inter;
            Pair max = Math.abs(before) > Math.abs(inter) ? new Pair(new Pair(attr,"<"), new Double(before)) :
                new Pair(new Pair(attr,"="), new Double(inter));
           // System.out.println("importance =: " + inter);
            double after =  classifier.importance(attr,">");
            
            after = Double.isNaN(after) ? 0 : after;
            max = Math.abs(((Double) max.right).doubleValue()) > Math.abs(after) ? max :
                new Pair(new Pair(attr, ">"), new Double(after));
        //    System.out.println("importance >: " + after);
        //    System.out.println("total: " + (before + inter + after));
            attrs[i] = max;
            //classifier.vote(attr,"good");
        }
        Arrays.sort(attrs, new Comparator(){
            
            public int compare(Object o1, Object o2) {
                Pair p1 = (Pair) o1;
                Pair p2 = (Pair) o2;
                
                return (int)  Double.compare(((Double) p2.right).doubleValue(), ((Double) p1.right).doubleValue());
            }
        });
        System.out.println("Sorted by importance:");
        for(int i = 0; i < attrs.length; ++i){
            System.out.println(attrs[i]);
        }
        int index = 0;
        /*for(;index < attrs.length; ++index){
         Pair p = attrs[index];
         if(((Double) p.right).doubleValue() > MIN_IMPORTANCE) break;
         }*/
        double averageTime  = 0;
        for(Iterator it = classifier.getOrders().iterator(); it.hasNext(); ){
            MyInstance instance = (MyInstance) it.next();
            averageTime += instance.getTime();
        }
        
        averageTime /= classifier.getOrders().size();
        if(Double.isNaN(averageTime)) return null;
        System.out.println("average time: " + averageTime);
        Constraints newConstraints = new Constraints(); 
        for(; index < attrs.length; ++index){
            Pair p = attrs[index];
            double importance = ((Double) p.right).doubleValue();
            double confidence = importance * (averageTime / MAX_WAIT_TIME);
            if(confidence < MIN_CONFIDENCE) continue;
            Assert._assert(!Double.isNaN(confidence));
            Pair pair = ((MyAttribute) ((Pair) p.left).left).pair;
            String value = (String) ((Pair) p.left).right;
            
            Pair left = (Pair) pair.left;
            Pair right = (Pair) pair.right;
            
            if(value.equals("<")){
                Constraint con = new BeforeConstraint((Relation) left.left, (org.sf.bddbddb.Attribute) left.right,
                    (Relation) right.left, (org.sf.bddbddb.Attribute) right.right, confidence);
                newConstraints.addBeforeConstraint(con);
            }else if(value.equals("=")){
                Constraint con = new InterleavedConstraint((Relation) left.left, (org.sf.bddbddb.Attribute) left.right,
                    (Relation) right.left, (org.sf.bddbddb.Attribute) right.right, confidence);
                newConstraints.addInterleavedConstraint(con);
            }else if(value.equals(">")){
                Constraint con = new BeforeConstraint((Relation) right.left, (org.sf.bddbddb.Attribute) right.right,
                    (Relation) left.left, (org.sf.bddbddb.Attribute) left.right, confidence);
                newConstraints.addBeforeConstraint(con);
            }
            
        }
        System.out.println(rule +" id: " + ruleIDs.get(rule.toString())+ " : \n before constraints: " + newConstraints.getBeforeConstraints());
        System.out.println("interleaved Constraints: " + newConstraints.getInterleavedConstraints());
        System.out.println("constraint graph: " + newConstraints.buildGraphAndReps().get(0) );
            System.out.println("constraint graph: " + newConstraints.buildGraphAndReps().get(0) );
        
        return newConstraints;
    }

    public String getOrder(){
        return bestOrder;
    }
    class TryThread extends Thread{
        File[][] bddFiles;
        String order, bddConfigName;
        
        long time = MAX_WAIT_TIME;
        public TryThread(String order,String bddConfigName, File[][] bddFiles){
            this.order = order;
            this.bddConfigName = bddConfigName;
            this.bddFiles = bddFiles;
        }
        public void run(){
            
            BDD result = null;
            BDD[] results = null;
            long tempTime = System.currentTimeMillis();
            BDDFactory factory = JFactory.init(rule.solver.BDDNODES, rule.solver.BDDCACHE);
            factory.setMaxIncrease(rule.solver.BDDNODES);
            BDDFactoryUtils.readBDDConfig(factory,bddConfigName);
            int[] varorder = factory.makeVarOrdering(false, order);
            factory.setVarOrder(varorder);
            
            BDD[] relationValues = relationValues = loadBDDs(factory,bddFiles[0]);;
            BDD[] canQuant = null;
            BDD[] rallRelationValues = null;
            if(bddFiles.length == 2){
                canQuant = loadBDDs(factory,bddFiles[1]);
            }else{
                rallRelationValues = loadBDDs(factory,bddFiles[1]);
                canQuant = loadBDDs(factory,bddFiles[2]);
            }
            
            if(rallRelationValues != null){
                results = rule.evalRelationsIncremental(factory,relationValues,rallRelationValues,canQuant);
            }else{
                result = rule.evalRelations(factory, relationValues, canQuant,0L);
            }
            time = System.currentTimeMillis() - tempTime;
            if(rallRelationValues != null){
                for(int i = 0; i < results.length; i++){
                    if(results[i] != null)
                        results[i].free();
                }
            }else
                result.free();
            
        }
    }
    
    /*Order Generation Routines */
    
    class TrainingOrderGenerator extends RoundedOrderGenerator{
        public TrainingOrderGenerator(List domains, String origOrder){
            super(domains,origOrder, SIZE_OF_TRAINING_SET);
        }
        
        public boolean hasNext(){ return triedOrders.size() < maxOrders; }
        
    }
    
    public class RoundedOrderGenerator extends OrderGenerator{
        public RoundedOrderGenerator(List domains, String origOrder, int numPermutations){
            super(domains,origOrder,numPermutations);
        }
        
        
        public RoundedOrderGenerator(List domains, String origOrder, int numPermutations, Set triedOrders){
            super(domains,origOrder,numPermutations, triedOrders);
        }
        
        public void resetRoundCounter(){ roundCounter = 0; }
        public boolean hasNext(){ return roundCounter < ROUND_SIZE && super.hasNext(); }  
    }
    
   public class LearnedOrderGenerator extends RoundedOrderGenerator{
        public LearnedOrderGenerator(List domains, String origOrder){
            super(domains,origOrder,MAX_PERMUTATIONS);
        }
        
        public LearnedOrderGenerator(List domains, String origOrder, Set triedOrders){
            super(domains,origOrder,MAX_PERMUTATIONS, triedOrders);
        }
    }
   public static class OrderGenerator{
        List domains;    
        int maxOrders;
        String origOrder;
        BigInteger numPossibleOrders;
        Set triedOrders;
        Set seenOrders;
        ArrayList lastOrder;
        int roundCounter = 0;
        
        public OrderGenerator(List domains, String origOrder, int numPermutations){
            this.domains = domains;
            this.origOrder = origOrder;
            this.triedOrders = new HashSet();
            this.seenOrders = new HashSet();
            roundCounter = 0;
            numPossibleOrders = getNumPosibleOrders(domains.size());
            System.out.println("Num possible orders of " + domains.size()
                + " domains: " + numPossibleOrders);
            maxOrders = Math.min(numPossibleOrders.intValue(), numPermutations);
        }
      
  
        public OrderGenerator(List domains, String origOrder, int numPermutations, Set triedOrders){
            this(domains,origOrder,numPermutations);
            this.triedOrders = triedOrders;
            seenOrders.addAll(this.triedOrders);
        }
        
        public BigInteger getNumPosibleOrders(int numDomains){
            //a permuted bell number of the number of Domains
            BigInteger sum = new BigInteger("0");
            for(int i = 1; i <= numDomains; ++i){
                sum = sum.add(modStirling(numDomains,i));
            }
            return sum;
        } 
        
        public BigInteger modStirling(int n, int k){         
            if(n == k) return PermutationGenerator.getFactorial(n);
            BigInteger sum = new BigInteger("0");    
            for(int i = 0; i < k; i++){
                long sign = (long) Math.pow(-1, i);
                BigInteger combo = combination(k, i);
                long lastPart = (long) Math.pow(k-i,n);
                long outside = sign * lastPart;
                BigInteger total = combo.multiply(new BigInteger(Long.toString(outside)));
                sum = sum.add(total);
            }   
            // formula specifies multiplication by 1/k! here, but we want the
            // permutatations of these partitions
            return sum;        
        }
        
        public BigInteger combination(int n, int k){
            if(k > n) return new BigInteger("0");
            if(k == 0) return new BigInteger("1");
            if(n == k) return new BigInteger("1");
            int diff, rest = 0;
            if(n - k >= k){
                diff = n - k;
                rest = k;
            }else{
                diff = k;
                rest = n - k;
            }
            BigInteger combination = new BigInteger("1");
            
            for(int i = n; i > diff; --i){
                combination = combination.multiply(new BigInteger(Integer.toString(i)));
            }
            
            return combination.divide(PermutationGenerator.getFactorial(rest));
        }

        public boolean existsMoreOrders(){ return seenOrders.size() < maxOrders; }
        public void addTriedOrder(List order){
            triedOrders.add(order);
        }
        
        public void resetSeenOrders(){
            seenOrders = new HashSet(triedOrders);
        }
        public boolean hasNext(){ return seenOrders.size() < maxOrders; }
        public String nextOrder(){
            
            do{
                lastOrder = getRandomPermutation(domains);
                //System.out.println("order: "+ lastOrder);
            }while(seenOrders.contains(lastOrder));
            
            seenOrders.add(lastOrder);
            
            StringBuffer varOrder = new StringBuffer(origOrder.replace('x','_'));
            boolean first = true;
            //    System.out.println("domain set: " + domainSet);
            //      System.out.println("orig: " + origOrder);
            for(int i = 0; i < lastOrder.size(); i++ ){
                int firstIndex = varOrder.length();
                BDDDomain firstDomain = null;
                for(int j = i; j < lastOrder.size(); j++){
                    List next2 = (List) lastOrder.get(j);
                    if(next2.size() == 1){ 
                        BDDDomain domain2 =(BDDDomain) next2.get(0);
                        int index = varOrder.indexOf(domain2.getName());
                        if(index < firstIndex){
                            firstIndex = index;
                            firstDomain = domain2;
                        }
                    }else{
                        for(Iterator jt = next2.iterator(); jt.hasNext();){
                            BDDDomain domain2 = (BDDDomain) jt.next();
                            int interIndex = varOrder.indexOf(domain2.getName());
                            if(interIndex < firstIndex){
                                firstIndex = interIndex;
                                firstDomain = domain2;
                            }
                        }
                        
                    }             
                    
                }
                //    System.out.println("first domain " + firstDomain + " at index "  + firstIndex);
                
                List next = (List) lastOrder.get(i);
                BDDDomain domain = (BDDDomain) next.get(0);
                int index = varOrder.indexOf(domain.getName());
                varOrder.replace(index,index + domain.getName().length(), firstDomain.getName());
                varOrder.replace(firstIndex,firstIndex + firstDomain.getName().length(), "");  
                StringBuffer domainString = new StringBuffer();
                domainString.append(domain.getName());
                if(next.size() != 1){
                    for(int j = 1; j < next.size(); j++){
                        BDDDomain domain2 = (BDDDomain) next.get(j);
                        domainString.append("x" + domain2.getName());
                        //int index2 = varOrder.indexOf(domain2.getName());
                        //Assert._assert(index2 != -1);
                        //System.out.println("Removing " + domain2.getName() + " at index: " + index2);
                        // varOrder.replace(index2, 1 + index2 + domain2.getName().length(),"");
                        String replace = varOrder.toString().replaceAll(domain2.getName() +"_","");
                        replace = replace.replaceAll("_" + domain2.getName(),"");
                        varOrder = new StringBuffer(replace);
                    }
                }
                
                varOrder.insert(firstIndex,domainString.toString());
            }
            ++roundCounter;
            return varOrder.toString();
        }
        
        
        
        //generate random set partitions using restricted growth function
        private ArrayList getRandomInterleaving(List domains){
            ArrayList ileave = new ArrayList();
            int[] growthString = new int[domains.size()];
            growthString[0] = 0;
            List list = new LinkedList();
            list.add(domains.get(0));
            ileave.add(list);
            for(int i = 1; i < growthString.length; i++){
                int randInt = Math.abs(randomNumGen.nextInt());
                int mod = 2 + max(growthString,0,i - 1);
                int setIndex = randInt % mod;
                growthString[i] = setIndex;
                if(ileave.size() == setIndex){
                    ileave.add(setIndex, new LinkedList());
                }
                List set = (List) ileave.get(setIndex);
                set.add(domains.get(i));
            }
            return ileave;
        }
        private ArrayList getRandomPermutation(ArrayList interDomains){
            ArrayList newOrder = new ArrayList(interDomains);
            for(int i = 0; i < newOrder.size(); i++){
                int num = Math.abs(randomNumGen.nextInt());
                num = num % (newOrder.size() - i);
                Object temp = newOrder.get(i + num);
                newOrder.set(i + num, newOrder.get(i));
                newOrder.set(i, temp);
            }
            return newOrder;
        }
        
        private int max(int[] array, int left, int right){
            int max = Integer.MIN_VALUE;
            for(int i = left; i <= right; i++){
                max = array[i] > max ? array[i] : max;
            }
            return max;
        }
        
        
        private ArrayList getRandomPermutation(List domains){
            return getRandomPermutation(getRandomInterleaving(domains));
        }
        
        
    }
    
    public static String orderListToString(List order){
        StringBuffer sb = new StringBuffer();
        for(Iterator it = order.iterator(); it.hasNext(); ){
            List domains = (List) it.next();
            BDDDomain domain = (BDDDomain) domains.get(0);
            sb.append(domain.getName());
            if(domains.size() > 1){
                Iterator jt = domains.iterator(); 
                jt.next();
                while(jt.hasNext()){
                    BDDDomain domain2 = (BDDDomain) jt.next();
                    sb.append("x" + domain2.getName());
                }
            }
            sb.append("_");
        }
        
        return sb.substring(0,sb.length() - 1).toString();
    }
    
    
    
    public static List parseOrder(String order, BDDSolver solver){
        StringTokenizer st = new StringTokenizer(order,"_");
        List orderList= new ArrayList();
        while(st.hasMoreTokens()){
            String domain = st.nextToken();
            StringTokenizer st2 = new StringTokenizer(domain,"x");
            List domains = new ArrayList();
            if(st2.countTokens() > 1){
                while(st2.hasMoreTokens()){
                    String iDomain = st2.nextToken();
                    domains.add(solver.getBDDDomain(iDomain));
                }
            }else{
                domains.add(solver.getBDDDomain(domain));
            }
            orderList.add(domains);
        }   
        return orderList;
    }
    
    public boolean isTrained(){ return isTrained; }
    

    public static class BDDFactoryUtils{
        public static void writeBDDConfig(BDDFactory bdd, String fileName) throws IOException {
            DataOutputStream dos = null;
            try {
                dos = new DataOutputStream(new FileOutputStream(fileName));
                for (int i = 0; i < bdd.numberOfDomains(); ++i) {
                    BDDDomain d = bdd.getDomain(i);
                    dos.writeBytes(d.getName()+" "+d.size()+"\n");
                }
            } finally {
                if (dos != null) dos.close();
            }
        }
        
        public static  void readBDDConfig(BDDFactory bdd, String filename) {
            BufferedReader in = null;
            try {
                in = new BufferedReader(new FileReader(filename));
                for (;;) {
                    String s = in.readLine();
                    if (s == null || s.equals("")) break;
                    StringTokenizer st = new StringTokenizer(s);
                    String name = st.nextToken();
                    long size = Long.parseLong(st.nextToken())-1;
                    makeDomain(bdd, name, BigInteger.valueOf(size).bitLength());
                }
            } catch (IOException x) {
            } finally {
                if (in != null) try { in.close(); } catch (IOException _) { }
            }
        }   
        
        private static BDDDomain makeDomain(BDDFactory bdd, String name, int bits) {
            BDDDomain d = bdd.extDomain(new long[] { 1L << bits })[0];
            d.setName(name);
            return d;
        }
        
    }
}
