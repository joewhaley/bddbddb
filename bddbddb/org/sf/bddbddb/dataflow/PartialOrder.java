/*
 * Created on Jul 13, 2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.dataflow;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.dataflow.PartialOrder.ConstraintGraph.ConstraintNavigator;
import org.sf.bddbddb.ir.IR;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.ir.OperationVisitor;
import org.sf.bddbddb.ir.dynamic.If;
import org.sf.bddbddb.ir.dynamic.Nop;
import org.sf.bddbddb.ir.highlevel.Copy;
import org.sf.bddbddb.ir.highlevel.Difference;
import org.sf.bddbddb.ir.highlevel.Free;
import org.sf.bddbddb.ir.highlevel.GenConstant;
import org.sf.bddbddb.ir.highlevel.Invert;
import org.sf.bddbddb.ir.highlevel.Join;
import org.sf.bddbddb.ir.highlevel.JoinConstant;
import org.sf.bddbddb.ir.highlevel.Load;
import org.sf.bddbddb.ir.highlevel.Project;
import org.sf.bddbddb.ir.highlevel.Rename;
import org.sf.bddbddb.ir.highlevel.Save;
import org.sf.bddbddb.ir.highlevel.Union;
import org.sf.bddbddb.ir.highlevel.Universe;
import org.sf.bddbddb.ir.highlevel.Zero;
import org.sf.bddbddb.ir.lowlevel.ApplyEx;
import org.sf.bddbddb.ir.lowlevel.Replace;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.HashWorklist;
import org.sf.bddbddb.util.MultiMap;
import org.sf.bddbddb.util.Navigator;
import org.sf.bddbddb.util.Pair;
import org.sf.bddbddb.util.UnionFind;

/**
 * @author Administrator
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class PartialOrder extends OperationProblem {
    IR ir;
    boolean TRACE = false;
    public PartialOrderFact currFact;

    public PartialOrder(IR ir) {
        this.ir = ir;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.dataflow.Problem#direction()
     */
    public boolean direction() {
        return true;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.dataflow.Problem#getTransferFunction(org.sf.bddbddb.ir.Operation)
     */
    public TransferFunction getTransferFunction(Operation o) {
        return new PartialOrderTF(o);
    }

    public String toString() {
        StringBuffer sb = new StringBuffer();
        for (Iterator it = operationFacts.entrySet().iterator(); it.hasNext();) {
            Map.Entry e = (Map.Entry) it.next();
            sb.append(e.getKey() + ": " + e.getValue() + "\n");
        }
        return sb.toString();
    }

    public Constraints getConstraints(Relation r) {
        return currFact.getConstraints(r);
    }
    public class PartialOrderFact implements OperationFact {
        Constraints[] constraintsMap;
        Operation op;
        IterationList loc;

        public PartialOrderFact() {
            constraintsMap = new Constraints[ir.solver.getNumberOfRelations()];
        }

        public Constraints getConstraints(Relation r) {
            return constraintsMap[r.id];
        }

        public Constraints[] getConstraintsMap() {
            return constraintsMap;
        }

        public void setConstraints(Relation r, Constraints constraints) {
            constraintsMap[r.id] = constraints;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.dataflow.OperationProblem.OperationFact#getOperation()
         */
        public Operation getOperation() {
            return op;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.dataflow.Problem.Fact#join(org.sf.bddbddb.dataflow.Problem.Fact)
         */
        public Fact join(Fact that) {
            PartialOrderFact result = (PartialOrderFact) copy(getLocation());
            PartialOrderFact thatFact = (PartialOrderFact) that;
            for (int i = 0; i < constraintsMap.length; i++) {
                result.constraintsMap[i].join(thatFact.constraintsMap[i]);
            }
            return result;
        }

        public boolean equals(Object o) {
            if (o instanceof PartialOrderFact) {
                PartialOrderFact that = (PartialOrderFact) o;
                return Arrays.equals(this.constraintsMap, that.constraintsMap);
            }
            return false;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.dataflow.Problem.Fact#copy(org.sf.bddbddb.IterationList)
         */
        public Fact copy(IterationList loc) {
            PartialOrderFact result = new PartialOrderFact();
            System.arraycopy(constraintsMap, 0, result.constraintsMap, 0, constraintsMap.length);
            result.loc = loc;
            return result;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.dataflow.Problem.Fact#setLocation(org.sf.bddbddb.IterationList)
         */
        public void setLocation(IterationList loc) {
            this.loc = loc;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.dataflow.Problem.Fact#getLocation()
         */
        public IterationList getLocation() {
            return loc;
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            sb.append("[ ");
            for (int i = 0; i < constraintsMap.length; i++) {
                Constraints c = constraintsMap[i];
                if (!c.isEmpty()) {
                    sb.append(ir.getRelation(i).toString() + ": ");
                    sb.append(c + " ");
                }
            }
            sb.append("]");
            return sb.toString();
        }
    }
    public class PartialOrderTF extends TransferFunction implements OperationVisitor {
        Operation op;

        public PartialOrderTF(Operation op) {
            this.op = op;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
         */
        public Fact apply(Fact f) {
            PartialOrderFact lastFact = (PartialOrderFact) f;
            currFact = (PartialOrderFact) lastFact.copy(lastFact.loc);
            op.visit(this);
            currFact.op = op;
            setFact(op, currFact);
            return currFact;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Join)
         */
        public Object visit(Join op) {
            if (TRACE) System.out.println(op);
            Relation src1 = op.getSrc1();
            Relation src2 = op.getSrc2();
            Relation dest = op.getRelationDest();
            Constraints union = visitUnionBinary(src1, src2);
            if (TRACE) System.out.println("union of src constraints: " + union);
            Constraints newCons = union.join(dest.getConstraints());
            if (TRACE) System.out.println("final constraints: " + newCons);
            currFact.setConstraints(op.getRelationDest(), newCons);
            return currFact;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Project)
         */
        public Object visit(Project op) {
            if (TRACE) System.out.println(op);
            Constraints c = currFact.getConstraints(op.getSrc());
            Constraints newCons = c.copy();
            if (TRACE) System.out.println("source constraints:" + c);
            List attrs = op.getAttributes();
            project(newCons, attrs);
            currFact.setConstraints(op.getRelationDest(), newCons);
            return currFact;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.ApplyEx)
         */
        public Object visit(ApplyEx op) {
            //decision
            if (TRACE) System.out.println(op);
            Constraints newCons = visitUnionBinary(op.getSrc1(), op.getSrc2());
            if (TRACE) System.out.println("union of source constraints: " + newCons);
            List attrs = op.getAttributes();
            project(newCons, attrs);
            Relation dest = op.getRelationDest();
            newCons.join(dest.getConstraints());
            if (TRACE) System.out.println("new constraints: " + newCons);
            currFact.setConstraints(dest, newCons);
            return currFact;
        }

        public Set project(Constraints cons, List attributes) {
            Pair rels = cons.getRelevantConstraints(attributes);
            Constraints relCs = new Constraints(cons.attributes, (Collection) rels.left, (Collection) rels.right);
            if (TRACE) System.out.println("relevant constraints: " + relCs);
            relCs.doTransitiveClosure();
            if (TRACE) System.out.println("transitive relevant constraints: " + relCs);
            cons.getBeforeConstraints().addAll(relCs.getBeforeConstraints());
            cons.getInterleavedConstraints().addAll(relCs.getInterleavedConstraints());
            Set removed = new HashSet();
            for (Iterator it = attributes.iterator(); it.hasNext();) {
                removed.addAll(cons.removeInvolving((Attribute) it.next()));
            }
            if (TRACE) System.out.println("removing: " + removed);
            return removed;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Rename)
         */
        public Object visit(Rename op) {
            if (TRACE) System.out.println(op);
            Constraints c = currFact.getConstraints(op.getSrc());
            BDDRelation dest = (BDDRelation) op.getRelationDest();
            Map renames = op.getRenameMap();
            List srcAttrs = op.getSrc().getAttributes();
            if (TRACE) System.out.println("src constraints: " + c);
            /*         if(TRACE) System.out.println("src attrs: " + srcAttrs);
             
             //Pair cons = c.getRelevantConstraints(srcAttrs);
             if(TRACE) System.out.println("relevant constraints: " + cons);
             */
            Constraints newCons = new Constraints(dest.getAttributes());
            for (Iterator it = c.getBeforeConstraints().iterator(); it.hasNext();) {
                Constraint oldC = (Constraint) it.next();
                Attribute a1 = (Attribute) renames.get(oldC.left);
                a1 = a1 != null ? a1 : (Attribute) oldC.left;
                Attribute a2 = (Attribute) renames.get(oldC.right);
                a2 = a2 != null ? a2 : (Attribute) oldC.right;
                newCons.addBeforeConstraint(new Constraint(a1, a2, oldC.confidence));
            }
            for (Iterator it = c.getInterleavedConstraints().iterator(); it.hasNext();) {
                Constraint oldC = (Constraint) it.next();
                Attribute a1 = (Attribute) renames.get(oldC.left);
                a1 = a1 != null ? a1 : (Attribute) oldC.left;
                Attribute a2 = (Attribute) renames.get(oldC.right);
                a2 = a2 != null ? a2 : (Attribute) oldC.right;
                newCons.addInterleavedConstraint(new Constraint(a1, a2, oldC.confidence));
            }
            newCons.join(dest.getConstraints());
            if (TRACE) System.out.println("new constraints: " + newCons);
            currFact.setConstraints(dest, newCons);
            return currFact;
        }

        public Constraints visitUnionBinary(Relation src1, Relation src2) {
            Constraints c1 = currFact.getConstraints(src1);
            Constraints c2 = currFact.getConstraints(src2);
            return c1.join(c2);
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Union)
         */
        public Object visit(Union op) {
            if (TRACE) System.out.println(op);
            Relation src1 = op.getSrc1();
            Relation src2 = op.getSrc2();
            Relation dest = op.getRelationDest();
            Constraints newCons = visitUnionBinary(src1, src2);
            if (TRACE) System.out.println("union of source constraints: " + newCons);
            newCons.join(dest.getConstraints());
            if (TRACE) System.out.println("new constraints: " + newCons);
            currFact.setConstraints(dest, newCons);
            return currFact;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Difference)
         */
        public Object visit(Difference op) {
            if (TRACE) System.out.println(op);
            Relation src1 = op.getSrc1();
            Relation src2 = op.getSrc2();
            Relation dest = op.getRelationDest();
            Constraints newCons = visitUnionBinary(src1, src2);
            if (TRACE) System.out.println("union of source constraints: " + newCons);
            newCons.join(dest.getConstraints());
            if (TRACE) System.out.println("new constraints: " + newCons);
            currFact.setConstraints(dest, newCons);
            return currFact;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Load)
         */
        public Object visit(Load op) {
            if (TRACE) System.out.println(op);
            Relation dest = op.getRelationDest();
            if (TRACE) System.out.println("relation constraints: " + dest.getConstraints());
            currFact.setConstraints(dest, dest.getConstraints());
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.JoinConstant)
         */
        public Object visit(JoinConstant op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.GenConstant)
         */
        public Object visit(GenConstant op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Free)
         */
        public Object visit(Free op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Universe)
         */
        public Object visit(Universe op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Zero)
         */
        public Object visit(Zero op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Invert)
         */
        public Object visit(Invert op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Copy)
         */
        public Object visit(Copy op) {
            currFact.setConstraints(op.getRelationDest(), currFact.getConstraints(op.getSrc()));
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Save)
         */
        public Object visit(Save op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.Replace)
         */
        public Object visit(Replace op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.If)
         */
        public Object visit(If op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.Nop)
         */
        public Object visit(Nop op) {
            return null;
        }
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
     */
    public Fact getBoundary() {
        PartialOrderFact fact = new PartialOrderFact();
        for (int i = 0; i < fact.constraintsMap.length; i++)
            fact.constraintsMap[i] = new Constraints(new LinkedList());
        return fact;
    }
    public static class Constraint extends Pair {
        public Constraint(Object left, Object right, double confidence) {
            super(left, right);
            this.confidence = confidence;
        }

        public Constraint(Object left, Object right) {
            super(left, right);
            confidence = 0;
        }
        double confidence;
    }
    public static class Constraints {
        static boolean TRACE = true;
        List/*Attribute*/attributes;
        MultiMap graph;
        UnionFind uf;
        Collection beforeConstraints;
        Collection interleavedConstraints;
        MultiMap repToAttributes = new GenericMultiMap();

        public Constraints(List attributes) {
            beforeConstraints = new LinkedHashSet();
            interleavedConstraints = new LinkedHashSet();
            this.attributes = attributes;
        }

        public Constraints(List attributes, Collection beforeConstraints, Collection interConstraints) {
            this.beforeConstraints = beforeConstraints;
            this.interleavedConstraints = interConstraints;
            this.attributes = attributes;
        }

        public Pair getRelevantConstraints(Collection attributes) {
            return new Pair(relevantBeforeConstraints(attributes), relevantInterConstraints(attributes));
        }

        public Collection getBeforeConstraints() {
            return beforeConstraints;
        }

        public Collection getInterleavedConstraints() {
            return interleavedConstraints;
        }

        private List relevantConstraints(Collection attributes, Collection srcCons) {
            List relevantConstraints = new LinkedList();
            for (Iterator it = srcCons.iterator(); it.hasNext();) {
                Constraint c = (Constraint) it.next();
                if (attributes.contains(c.left) || attributes.contains(c.right)) relevantConstraints.add(c);
            }
            return relevantConstraints;
        }

        public List relevantBeforeConstraints(Collection attributes) {
            return relevantConstraints(attributes, beforeConstraints);
        }

        public List relevantInterConstraints(Collection attributes) {
            return relevantConstraints(attributes, interleavedConstraints);
        }

        public void addBeforeConstraint(Pair p) {
            beforeConstraints.add(p);
        }

        public void addInterleavedConstraint(Pair p) {
            interleavedConstraints.add(p);
        }

        public Constraints copy() {
            Constraints c = new Constraints(new LinkedList(attributes));
            c.beforeConstraints = new HashSet(this.beforeConstraints);
            c.interleavedConstraints = new HashSet(this.interleavedConstraints);
            return c;
        }

        public List removeInvolving(Attribute a) {
            List removed = new LinkedList();
            removed.addAll(removeInvolving(a, beforeConstraints));
            removed.addAll(removeInvolving(a, interleavedConstraints));
            return removed;
        }

        private List removeInvolving(Attribute a, Collection cons) {
            List removed = new LinkedList();
            for (Iterator it = cons.iterator(); it.hasNext();) {
                Constraint c = (Constraint) it.next();
                if (c.contains(a)) {
                    removed.add(c);
                    it.remove();
                }
            }
            return removed;
        }

        public List isSatisifiable() {
            ConstraintGraph graph = new ConstraintGraph();
            uf = new UnionFind(4096);
            for (Iterator it = interleavedConstraints.iterator(); it.hasNext();) {
                Pair p = (Pair) it.next();
                Object repl = uf.find(p.left);
                Object repr = uf.find(p.right);
                if (repl == null && repr == null) {
                    uf.union(p.left, p.right);
                } else if (repl != null && repr == null) {
                    uf.union(repl, p.right);
                } else if (repl == null && repr != null) {
                    uf.union(p.left, repr);
                } else {
                    uf.union(repl, repr);
                }
            }
            Set nodes = new HashSet();
            for (Iterator it = attributes.iterator(); it.hasNext();) {
                Object o = it.next();
                Object rep = uf.find(o);
                graph.addNode(rep);
                repToAttributes.add(rep, o);
            }
            for (Iterator it = beforeConstraints.iterator(); it.hasNext();) {
                Pair p = (Pair) it.next();
                Object repl = uf.find(p.left);
                Object repr = uf.find(p.right);
                if (repl == null && repr == null) {
                    graph.addEdge(p.left, p.right);
                } else if (repl != null && repr == null) {
                    graph.addEdge(repl, p.right);
                } else if (repl == null && repr != null) {
                    graph.addEdge(p.left, repr);
                } else {
                    graph.addEdge(repl, repr);
                }
            }
            List cycles = new LinkedList();
            Set visited = new HashSet();
            for (Iterator it = graph.nodes.iterator(); it.hasNext();) {
                Object o = it.next();
                if (!visited.contains(o)) {
                    cycles.addAll(findCycles(o, visited, new LinkedList(), graph.getNavigator()));
                }
            }
            if (TRACE && cycles.size() != 0) System.out.println("Not satisfiable, cycles found: " + cycles);
            return cycles;
        }

        List findCycles(Object start, Set visited, List trace, ConstraintNavigator nav) {
            List cycles = new LinkedList();
            trace.add(start);
            visited.add(start);
            Collection nexts = nav.next(start);
            for (Iterator it = nexts.iterator(); it.hasNext();) {
                Object next = it.next();
                if (visited.contains(next)) {
                    if (trace.contains(next)) {
                        int index = trace.indexOf(next);
                        List cycle = new LinkedList(trace.subList(index, trace.size()));
                        cycles.add(cycle);
                    }
                } else {
                    cycles.addAll(findCycles(next, visited, trace, nav));
                }
            }
            trace.remove(trace.size() - 1);
            return cycles;
        }

        List cycleToConstraints(List cycle) {
            List constraints = new LinkedList();
            for (ListIterator it = cycle.listIterator(); it.hasNext();) {
                Object o1 = it.next();
                if (it.hasNext()) {
                    constraints.addAll(constraints(o1, it.next()));
                    it.previous();
                }
            }
            constraints.addAll(constraints(cycle.get(cycle.size() - 1), cycle.get(0)));
            return constraints;
        }

        List constraints(Object o1, Object o2) {
            List constraints = new LinkedList();
            Collection o1jects = repToAttributes.getValues(o1);
            Collection o2jects = repToAttributes.getValues(o2);
            for (Iterator it = o1jects.iterator(); it.hasNext();) {
                Attribute left = (Attribute) it.next();
                for (Iterator jt = o2jects.iterator(); jt.hasNext();) {
                    Constraint p = new Constraint(left, (Attribute) jt.next(), 0);
                    if (beforeConstraints.contains(p)) {
                        constraints.add(p);
                    }
                }
            }
            return constraints;
        }

        void breakCycles(List cycles) {
            List ccycles = new LinkedList();
            for (Iterator it = cycles.iterator(); it.hasNext();) {
                List cycle = cycleToConstraints((List) it.next());
                ccycles.add(cycle);
            }
            Iterator it = ccycles.iterator();
            List lowest = (List) it.next();
            int lowestRate = rateCycle(lowest);
            for (; it.hasNext();) {
                List next = (List) it.next();
                int nextRate = rateCycle(next);
                if (nextRate < lowestRate) {
                    lowest = next;
                    lowestRate = nextRate;
                }
            }
            breakConstraintCycle(lowest);
        }

        int rateCycle(List cycle) {
            int i = 0;
            int sum = 0;
            for (; i < cycle.size(); i++) {
                sum += ((Constraint) cycle.get(i)).confidence;
            }
            return sum / i;
        }

        void breakConstraintCycle(List cycle) {
            Iterator jt = cycle.iterator();
            Constraint lowest = (Constraint) jt.next();
            for (; jt.hasNext();) {
                Constraint next = (Constraint) jt.next();
                if (next.confidence < lowest.confidence) lowest = next;
                /* TODO depending on granularity of confidence, add ability to
                 * choose between relatively similar ones.
                 */
            }
            beforeConstraints.remove(lowest);
        }

        public void satisfy() {
            List cycles = null;
            while ((cycles = isSatisifiable()).size() != 0) {
                breakCycles(cycles);
            }
        }

        public Constraints join(Constraints that) {
            List resultAttributes = new LinkedList(attributes);
            resultAttributes.addAll(that.attributes);
            Constraints result = new Constraints(resultAttributes);
            result.beforeConstraints = new HashSet(this.beforeConstraints);
            result.beforeConstraints.addAll(that.beforeConstraints);
            result.interleavedConstraints = new HashSet(this.interleavedConstraints);
            result.interleavedConstraints.addAll(that.interleavedConstraints);
            result.satisfy();
            return result;
        }

        public boolean isEmpty() {
            return beforeConstraints.isEmpty() && interleavedConstraints.isEmpty();
        }

        public boolean equals(Object o) {
            if (o instanceof Constraints) {
                Constraints that = (Constraints) o;
                return this.attributes.equals(that.attributes) && this.beforeConstraints.equals(that.beforeConstraints)
                    && this.interleavedConstraints.equals(that.interleavedConstraints);
            }
            return false;
        }

        public String toString() {
            return "[before constraints: " + beforeConstraints + " interleaved constraints: " + interleavedConstraints + "]";
        }

        public void doTransitiveClosure() {
            beforeConstraints = doTransitiveClosure(attributes, beforeConstraints);
            interleavedConstraints = doTransitiveClosure(attributes, interleavedConstraints);
        }

        public Collection doTransitiveClosure(Collection attributes, Collection constraints) {
            ConstraintGraph graph = new ConstraintGraph(attributes, constraints);
            Collection newConstraints = new LinkedHashSet(constraints);
            ConstraintGraph.ConstraintNavigator nav = graph.getNavigator();
            HashWorklist w = new HashWorklist(true);
            w.addAll(constraints);
            //transitive closure
            while (!w.isEmpty()) {
                Pair pair = (Pair) w.pull();
                Object left = pair.left;
                Object right = pair.right;
                Collection nexts = nav.next(right);
                for (Iterator it = nexts.iterator(); it.hasNext();) {
                    Object trans = it.next();
                    newConstraints.add(new Constraint(left, trans)); //consider confidence
                    w.add(new Pair(left, trans));
                }
            }
            return newConstraints;
        }
    }
    public static class ConstraintGraph {
        MultiMap graph;
        Collection nodes;
        ConstraintNavigator nav;

        public ConstraintGraph() {
            nav = new ConstraintNavigator();
            graph = new GenericMultiMap();
            nodes = new HashSet();
        }

        public ConstraintGraph(Collection constraints) {
            this();
            for (Iterator it = constraints.iterator(); it.hasNext();) {
                Pair p = (Pair) it.next();
                Object o1 = p.left;
                Object o2 = p.right;
                graph.add(o1, o2);
                nodes.add(o1);
                nodes.add(o2);
            }
        }

        public ConstraintGraph(Collection nodes, Collection constraints) {
            this();
            this.nodes.addAll(nodes);
            for (Iterator it = constraints.iterator(); it.hasNext();) {
                Pair p = (Pair) it.next();
                Object o1 = p.left;
                Object o2 = p.right;
                graph.add(o1, o2);
            }
        }

        public void addEdge(Object o1, Object o2) {
            graph.add(o1, o2);
        }

        public void removeEdge(Object o1, Object o2) {
            graph.remove(o1, o2);
            if (graph.get(o1) == null) nodes.remove(o1);
            if (!graph.containsValue(o2)) nodes.remove(o2);
        }

        public void removeEdgesFrom(Object o) {
            graph.remove(o);
        }

        public void addNode(Object o) {
            nodes.add(o);
        }

        public void removeNode(Object o) {
            nodes.remove(o);
        }

        public boolean isCycle(List cycle) {
            Collection keys = new HashSet(graph.keySet());
            Set visited = new HashSet();
            for (Iterator it = keys.iterator(); it.hasNext();) {
                Object obj = it.next();
                if (!visited.contains(obj)) if (isPath(obj, obj, visited, cycle)) return true;
            }
            return false;
        }

        public boolean isPath(Object start, Object end, List path) {
            return isPath(start, end, new HashSet(), path);
        }

        private boolean isPath(Object start, Object target, Set visited, List path) {
            path.add(start);
            visited.add(start);
            Collection nexts = graph.getValues(start);
            for (Iterator it = nexts.iterator(); it.hasNext();) {
                Object next = it.next();
                if (next == target) {
                    return true;
                }
                if (!visited.contains(next)) if (isPath(next, target, visited, path)) return true;
            }
            path.remove(start);
            return false;
        }

        public Collection getRoots() {
            Set roots = new HashSet(nodes);
            roots.removeAll(graph.values());
            return roots;
        }

        public String toString() {
            return graph.toString();
        }

        public ConstraintNavigator getNavigator() {
            return nav;
        }
        public class ConstraintNavigator implements Navigator {
            /* (non-Javadoc)
             * @see org.sf.bddbddb.util.Navigator#next(java.lang.Object)
             */
            public Collection next(Object node) {
                return graph.getValues(node);
            }

            /* (non-Javadoc)
             * @see org.sf.bddbddb.util.Navigator#prev(java.lang.Object)
             */
            public Collection prev(Object node) {
                throw new UnsupportedOperationException();
            }
        }
    }
}