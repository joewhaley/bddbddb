// Learner.java, created Sep 3, 2004 8:57:36 PM 2004 by mcarbin
// Copyright (C) 2004 Michael Carbin <mcarbin@stanford.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import jwutil.collections.GenericMultiMap;
import jwutil.collections.LinearSet;
import jwutil.collections.MultiMap;
import jwutil.collections.UnionFind;
import jwutil.util.Assert;
import org.sf.bddbddb.dataflow.PartialOrder.Constraint;
import org.sf.bddbddb.dataflow.PartialOrder.ConstraintGraph;
import org.sf.bddbddb.dataflow.PartialOrder.Constraints;
import org.sf.bddbddb.ir.PartialOrderDomainAssignment;
import org.sf.javabdd.BDDDomain;

/**
 * Learner
 * 
 * @author mcarbin
 * @version $Id$
 */
public interface Learner {
    
    public void learn();
    
    public static class IndividualRuleLearner implements Learner{
        public BDDSolver solver;
        public Stratify stratify;
        public IndividualRuleLearner(BDDSolver solver, Stratify stratify){
            this.solver = solver;
            this.stratify = stratify;
            
        }
        /* (non-Javadoc)
         * @see org.sf.bddbddb.Learner#Learner(org.sf.bddbddb.BDDSolver)
         */
        public void learn(){
            System.out.println("learning pass");
            List rulesToLearn = solver.rulesToLearn();
            TreeSet constraints = new TreeSet();
            for(Iterator it = rulesToLearn.iterator(); it.hasNext(); ){
                
                BDDInferenceRule rule = (BDDInferenceRule) it.next();
                
                Assert._assert(rule != null);
                System.out.println("Learning: " + rule);
                rule.learn();
                Assert._assert(rule.getLearnedOrder() != null);
                Constraints ruleCons = rule.getLearnedOrder().getConstraints();
                if(ruleCons == null) continue;
                constraints.addAll(ruleCons.getAllConstraints());
                rule.getLearnedOrder().saveConstraints();
            }
            System.out.println("all learned constraints: " + constraints);
            ConstraintGraph graph = new ConstraintGraph();
            UnionFind uf = new UnionFind(4096);
            MultiMap domainMap = solver.getBDDDomains();
            graph.addNodes(domainMap.values());
            System.out.println("nodes: " + graph.getNodes());
            List dummyCycle = new LinkedList();
            for(Iterator it = constraints.iterator(); it.hasNext(); ){   
                Constraint con = (Constraint) it.next();
                BDDRelation leftRelation = (BDDRelation) con.getLeftRelation();
                BDDRelation rightRelation = (BDDRelation) con.getRightRelation();
                BDDDomain leftDomain = leftRelation.getBDDDomain(con.getLeftAttribute());
                BDDDomain rightDomain = rightRelation.getBDDDomain(con.getRightAttribute());
                Object leftRep = uf.find(leftDomain);
                Object rightRep = uf.find(rightDomain);
                
                if(con.getType() == Constraint.BEFORE){
                        graph.addEdge(leftRep,rightRep);
                    if(graph.isCycle(dummyCycle))
                        graph.removeEdge(leftRep, rightRep);
                   
                }else if(con.getType() == Constraint.INTERLEAVED){
                    System.out.println("before nodes: " + graph.getNodes() + " constraint: " + con);
                    
                    ConstraintGraph testGraph = new ConstraintGraph(graph);
                    uf.union(leftRep,rightRep);
                    testGraph.update(uf);
                    if(!testGraph.isCycle(dummyCycle))
                        graph = testGraph;
                    System.out.println("after nodes: " + graph.getNodes());
                }
              
            }
            System.out.println("learned constraint graph: " + graph);
            MultiMap interleaves = new GenericMultiMap();
            Map domainReflect = new HashMap();
            for(Iterator it = domainMap.values().iterator(); it.hasNext(); ){
               
                Object obj = it.next();
                domainReflect.put(obj,obj);
                interleaves.add(uf.find(obj), obj);
            }
            for(Iterator it = interleaves.keySet().iterator(); it.hasNext(); ){
                Collection c =  interleaves.getValues(it.next());
                if(c.size() <= 1)
                    it.remove();
            }
            
            System.out.println("interleaves: " + interleaves);
            System.out.println("domain reflect:" + domainReflect);
            String order = PartialOrderDomainAssignment.graphToOrder(true,graph,uf,interleaves,domainReflect);
          solver.VARORDER = order;
          solver.setVariableOrdering();
            /*    System.setProperty("allopts", "");
            IR ir = IR.create(stratify);
            ir.optimize();
         */
        }
    }
    
    public static class EnsembleLearner implements Learner{
        BDDSolver solver;
        public EnsembleLearner(BDDSolver solver){
            this.solver = solver;
        }
        /* (non-Javadoc)
         * @see org.sf.bddbddb.Learner#learn()
         */
        public void learn() {
            List rules = solver.rulesToLearn();
            //LearnedOrder[] lOrders = new learnedOrder[rules.size()];
            //for(int i = 0; i < ; it.hasNext(); ){
                
            //}
            LinearSet domains = new LinearSet();
            MultiMap domainMap = solver.getBDDDomains();
            domains.addAll(domainMap.values());
            
        }
        
    }
}
