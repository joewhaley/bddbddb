package org.sf.bddbddb.ir;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import org.sf.bddbddb.IterationFlowGraph;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.Solver;
import org.sf.bddbddb.Stratify;
import org.sf.bddbddb.dataflow.ConstantProp;
import org.sf.bddbddb.dataflow.DataflowSolver;
import org.sf.bddbddb.dataflow.Liveness;
import org.sf.bddbddb.dataflow.Problem;
import org.sf.bddbddb.dataflow.ConstantProp.ConstantPropFacts;
import org.sf.bddbddb.dataflow.DataflowSolver.DataflowIterator;
import org.sf.bddbddb.dataflow.Liveness.LivenessFact;
import org.sf.bddbddb.ir.highlevel.Free;
import org.sf.bddbddb.ir.highlevel.Load;
import org.sf.bddbddb.ir.highlevel.Save;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.MultiMap;

/**
 * @author Collective
 */
public class IR {
    
    public Solver solver;
    IterationFlowGraph graph;
    
    boolean FREE_DEAD = !System.getProperty("freedead", "no").equals("no");
    boolean CONSTANTPROP = !System.getProperty("constantprop", "no").equals(
        "no");
    boolean TRACE;
    
    public static IR create(Stratify s) {
        return create(s.solver, s.firstSCCs, s.innerSCCs);
    }
    
    public static IR create(Solver solver, List firstSCCs, MultiMap innerSCCs) {
        IterationFlowGraph ifg = new IterationFlowGraph(solver.getRules(), firstSCCs, innerSCCs);
        IterationList list = ifg.expand();
        // Add load operations.
        if (!solver.getRelationsToLoad().isEmpty()) {
            Assert._assert(!list.isLoop());
            IterationList loadList = new IterationList(false);
            for (Iterator j = solver.getRelationsToLoad().iterator(); j.hasNext(); ) {
                Relation r = (Relation) j.next();
                loadList.addElement(new Load(r));
            }
            list.addElement(0, loadList);
        }
        // Add save operations.
        if (!solver.getRelationsToSave().isEmpty()) {
            Assert._assert(!list.isLoop());
            IterationList saveList = new IterationList(false);
            for (Iterator j = solver.getRelationsToSave().iterator(); j.hasNext(); ) {
                Relation r = (Relation) j.next();
                saveList.addElement(new Save(r));
            }
            list.addElement(saveList);
        }
        return new IR(solver, ifg);
    }
    
    public void optimize() {
        if (CONSTANTPROP) {
            DataflowSolver df_solver = new DataflowSolver();
            Problem problem = new ConstantProp();
            IterationList list = graph.getIterationList();
            df_solver.solve(problem, list);
            DataflowIterator di = df_solver.getIterator(problem, list);
            while (di.hasNext()) {
                Object o = di.next();
                if (TRACE) System.out.println("Next: " + o);
                if (o instanceof Operation) {
                    Operation op = (Operation) o;
                    ConstantPropFacts f = (ConstantPropFacts) di.getFact();
                    Operation op2 = ((ConstantProp) problem)
                        .simplify(op, f);
                    if (op != op2) {
                        if (TRACE) System.out.println("Replacing " + op
                            + " with " + op2);
                        di.set(op2);
                    }
                } else {
                    IterationList b = (IterationList) o;
                    di.enter(b);
                }
            }
        }
        if (FREE_DEAD) {
            DataflowSolver df_solver = new DataflowSolver();
            Liveness problem = new Liveness(this);
            IterationList list = graph.getIterationList();
            df_solver.solve(problem, list);
            DataflowIterator di = df_solver.getIterator(problem, list);
            List srcs = new LinkedList();
            doLiveness(list, srcs, problem);
        }
        
    }
    
    void doLiveness(IterationList list, List srcs, Liveness p) {
        ListIterator it = list.iterator();
        while (it.hasNext()) {
            Object o = it.next();
            if (TRACE) System.out.println("Next: " + o);
            if (o instanceof Operation) {
                Operation op = (Operation) o;
                LivenessFact fact = (LivenessFact) p.currentFacts.getFact(op);
                for (Iterator it2 = srcs.iterator(); it2.hasNext();) {
                    Relation r = (Relation) it2.next();
                    if (!fact.isAlive(r)) {
                        Free free = new Free(r);
                        if (TRACE) System.out.println("Adding a free for " + r);
                        it.previous();
                        it.add(free);
                        it.next();
                    }
                }
                srcs = op.getSrcs();
            } else {
                IterationList b = (IterationList) o;
                doLiveness(b, srcs, p);
            }
        }
    }
    
    public void interpret() {
        Interpreter interpret = solver.getInterpreter();
        IterationList list = graph.getIterationList();
        list.interpret(interpret);
    }
    
    /**
     * 
     */
    private IR(Solver solver, IterationFlowGraph g) {
        this.solver = solver;
        this.graph = g;
    }
    
    public Relation getRelation(String name) {
        return solver.getRelation(name);
    }
    
    public Relation getRelation(int index) {
        return solver.getRelation(index);
    }
    
    public int getNumberOfRelations() {
        return solver.getNumberOfRelations();
    }
}
