package org.sf.bddbddb.ir;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.IterationFlowGraph;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.Solver;
import org.sf.bddbddb.Stratify;
import org.sf.bddbddb.dataflow.ConstantProp;
import org.sf.bddbddb.dataflow.DataflowSolver;
import org.sf.bddbddb.dataflow.DefUse;
import org.sf.bddbddb.dataflow.Liveness;
import org.sf.bddbddb.dataflow.Problem;
import org.sf.bddbddb.dataflow.ConstantProp.ConstantPropFacts;
import org.sf.bddbddb.dataflow.DataflowSolver.DataflowIterator;
import org.sf.bddbddb.dataflow.DefUse.DefUseFact;
import org.sf.bddbddb.dataflow.Liveness.LivenessFact;
import org.sf.bddbddb.ir.highlevel.BooleanOperation;
import org.sf.bddbddb.ir.highlevel.Copy;
import org.sf.bddbddb.ir.highlevel.Free;
import org.sf.bddbddb.ir.highlevel.Load;
import org.sf.bddbddb.ir.highlevel.Project;
import org.sf.bddbddb.ir.highlevel.Rename;
import org.sf.bddbddb.ir.highlevel.Save;
import org.sf.bddbddb.ir.lowlevel.ApplyEx;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.MultiMap;
import org.sf.javabdd.BDDFactory.BDDOp;

/**
 * @author Collective
 */
public class IR {

    public Solver solver;

    public IterationFlowGraph graph;

    boolean ALL_OPTS = !System.getProperty("allopts", "no").equals("no");
    boolean FREE_DEAD = ALL_OPTS || !System.getProperty("freedead", "no").equals("no");
    boolean CONSTANTPROP = ALL_OPTS || !System.getProperty("constantprop", "no").equals("no");
    boolean DEFUSE = ALL_OPTS || !System.getProperty("defuse", "no").equals("no");
    boolean DOMAIN_ASSIGNMENT = ALL_OPTS || !System.getProperty("domainassign", "no").equals("no");

    boolean TRACE = false;

    public static IR create(Stratify s) {
        return create(s.solver, s.firstSCCs, s.innerSCCs);
    }

    public static IR create(Solver solver, List firstSCCs, MultiMap innerSCCs) {
        IterationFlowGraph ifg = new IterationFlowGraph(solver.getRules(),
            firstSCCs, innerSCCs);
        IterationList list = ifg.expand();
        // Add load operations.
        if (!solver.getRelationsToLoad().isEmpty()) {
            Assert._assert(!list.isLoop());
            IterationList loadList = new IterationList(false);
            for (Iterator j = solver.getRelationsToLoad().iterator(); j.hasNext();) {
                Relation r = (Relation) j.next();
                loadList.addElement(new Load(r, solver.basedir+r+".bdd", false));
            }
            list.addElement(0, loadList);
        }
        // Add save operations.
        if (!solver.getRelationsToSave().isEmpty()) {
            Assert._assert(!list.isLoop());
            IterationList saveList = new IterationList(false);
            for (Iterator j = solver.getRelationsToSave().iterator(); j
                .hasNext();) {
                Relation r = (Relation) j.next();
                saveList.addElement(new Save(r, solver.basedir+r+".bdd", false));
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
                    Operation op2 = ((ConstantProp) problem).simplify(op, f);
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

        if (DEFUSE) {
            while (doDefUse()) ;
        }
        doPeephole(graph.getIterationList());
        if (FREE_DEAD) {
            DataflowSolver df_solver = new DataflowSolver();
            Liveness problem = new Liveness(this);
            IterationList list = graph.getIterationList();
            df_solver.solve(problem, list);
            DataflowIterator di = df_solver.getIterator(problem, list);
            List srcs = new LinkedList();
            doLiveness(list, srcs, problem);
        }
        if (DOMAIN_ASSIGNMENT) {
            DomainAssignment ass = new UFDomainAssignment(solver);
            IterationList list = graph.getIterationList();
            ass.addConstraints(list);
            ass.doAssignment();
            cleanUpAfterAssignment(list);
        }
    }

    void cleanUpAfterAssignment(IterationList list) {
        for (ListIterator i = list.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (o instanceof Rename) {
                i.remove();
                Rename r = (Rename) o;
                Relation r0 = r.getRelationDest();
                Relation r1 = r.getSrc();
                Copy op = new Copy(r0, r1);
                i.add(op);
            } else if (o instanceof IterationList) {
                cleanUpAfterAssignment((IterationList) o);
            }
        }
    }
    
    void doPeephole(IterationList list) {
        for (ListIterator i = list.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (o instanceof Copy) {
                Copy op = (Copy) o;
                if (op.getRelationDest() == op.getSrc())
                    i.remove();
            } else if (o instanceof IterationList) {
                doPeephole((IterationList) o);
            }
        }
    }
    
    boolean doDefUse() {
        boolean change = false;
        DataflowSolver df_solver = new DataflowSolver();
        DefUse problem = new DefUse(this);
        IterationList list = graph.getIterationList();
        df_solver.solve(problem, list);
        DataflowIterator di = df_solver.getIterator(problem, list);
        List to_remove = new LinkedList();
    outer:
        while (di.hasNext()) {
            Object o = di.next();
            if (TRACE) System.out.println("Next: " + o);
            if (o instanceof Operation) {
                Operation op = (Operation) o;
                DefUseFact f = (DefUseFact) di.getFact();
                if (op.getRelationDest() != null) {
                    Collection uses = problem.getUses(op.getRelationDest());
                    if (TRACE) System.out.println("Uses: " + uses);
                    if (uses.size() == 0) {
                        if (TRACE) System.out.println("Removing: " + op);
                        di.remove();
                        change = true;
                        continue;
                    }
                }
                if (op instanceof Project) {
                    Project p = (Project) op;
                    Relation src = p.getSrc();
                    Set defs = f.getReachingDefs(src);
                    if (TRACE) System.out.println("Defs: " + defs);
                    if (defs.size() == 1) {
                        Operation op2 = (Operation) defs.iterator().next();
                        if (op2 instanceof BooleanOperation) {
                            BooleanOperation boolop = (BooleanOperation) op2;
                            // check if this specific def reaches any other uses.
                            Set uses = problem.getUses(src);
                            if (TRACE) System.out.println("Uses of "+src+": " + uses);
                            for (Iterator i = uses.iterator(); i.hasNext(); ) {
                                Operation other = (Operation) i.next();
                                if (other == p) continue;
                                DefUseFact duf2 = (DefUseFact) problem.getFact(other);
                                if (duf2.getReachingDefs(src).contains(boolop)) {
                                    continue outer;
                                }
                            }
                            BDDOp bddop = boolop.getBDDOp();
                            ApplyEx new_op = new ApplyEx((BDDRelation) p.getRelationDest(), (BDDRelation) boolop.getSrc1(), bddop, (BDDRelation) boolop.getSrc2());
                            if (TRACE) System.out.println("Replacing " + op + " with " + new_op);
                            di.set(new_op);
                            if (TRACE) System.out.println("Marking "+boolop+" for deletion.");
                            to_remove.add(boolop);
                        }
                    }
                }
            } else {
                IterationList b = (IterationList) o;
                di.enter(b);
            }
        }
        if (!to_remove.isEmpty()) {
            list.removeElements(to_remove);
            change = true;
        }
        return change;
    }
    
    void doLiveness(IterationList list, List srcs, Liveness p) {
        ListIterator it = list.iterator();
        while (it.hasNext()) {
            Object o = it.next();
            if (TRACE) System.out.println("Next: " + o);
            if (o instanceof Operation) {
                Operation op = (Operation) o;
                LivenessFact fact = (LivenessFact) p.getFact(op);
                if (TRACE) System.out.println("Live: " + fact);
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
        //printIR();
        BDDInterpreter interpret = (BDDInterpreter) solver.getInterpreter();
        if (DOMAIN_ASSIGNMENT) interpret.needsDomainMatch = false;
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

    public void printIR() {
        printIR(graph.getIterationList(), "");
    }

    public void printIR(IterationList list, String space) {
        System.out.println(space + list + ":");
        for (Iterator it = list.iterator(); it.hasNext();) {
            Object o = it.next();
            if (o instanceof Operation) {
                System.out.println(space + "  " + o + "    " + getRenames((Operation) o));
            } else {
                printIR((IterationList) o, space + "  ");
            }
        }
    }
    public String getRenames(Operation op) {
        BDDRelation r0 = (BDDRelation) op.getRelationDest();
        if (r0 == null) return "";
        List srcs = op.getSrcs();
        StringBuffer sb = new StringBuffer();
        for (Iterator i = srcs.iterator(); i.hasNext(); ) {
            BDDRelation r2 = (BDDRelation) i.next();
            sb.append(Operation.getRenames(r2, r0));
        }
        if (sb.length() == 0) return "";
        return sb.substring(1);
    }
    
}