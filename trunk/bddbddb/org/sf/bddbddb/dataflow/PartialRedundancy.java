/*
 * Created on Jul 6, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.dataflow;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.Solver;
import org.sf.bddbddb.dataflow.OperationProblem.OperationFact;
import org.sf.bddbddb.dataflow.PartialRedundancy.Anticipated.AnticipatedFact;
import org.sf.bddbddb.dataflow.PartialRedundancy.Available.AvailableFact;
import org.sf.bddbddb.dataflow.PartialRedundancy.Earliest.EarliestFact;
import org.sf.bddbddb.dataflow.PartialRedundancy.Latest.LatestFact;
import org.sf.bddbddb.dataflow.Problem.Fact;
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

/**
 * @author mcarbin
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class PartialRedundancy implements IRPass {
    public Map opToExpression;
    public GetExpressions getExpressions;
    public Anticipated anticipated;
    public Available available;
    public Earliest earliest;
    public Used used;
    public Postponed postponed;
    public Latest latest;
    Solver solver;
    IR ir;
    Set allExpressions;
    boolean TRACE = false;

    public PartialRedundancy(IR ir) {
        this.ir = ir;
        this.solver = ir.solver;
        opToExpression = new HashMap();
        getExpressions = new GetExpressions();
        anticipated = new Anticipated();
        available = new Available();
        earliest = new Earliest();
        used = new Used();
        allExpressions = new HashSet();
        postponed = new Postponed();
        latest = new Latest();
        initialize(ir.graph.getIterationList());
    }

    public void initialize(IterationList list) {
        for (ListIterator it = list.iterator(); it.hasNext();) {
            Object o = it.next();
            if (o instanceof IterationList) {
                IterationList l = (IterationList) o;
                if (l.isLoop()) {
                    if (TRACE) System.out.println("Adding nop to " + l + "'s loop edge");
                    l.getLoopEdge().addElement(new Nop());
                    IterationList newList = new IterationList(false);
                    newList.addElement(new Nop());
                    it.previous();
                    if (TRACE) System.out.println("Add new list with nop in front of" + l);
                    it.add(newList);
                    it.next();
                }
                initialize(l);
            } else {
                Operation op = (Operation) o;
                op.visit(getExpressions);
            }
        }
    }

    public boolean run() {
        IterationList list = ir.graph.getIterationList();
        DataflowSolver solver = new DataflowSolver();
        solver.solve(anticipated, list);
        solver = new DataflowSolver();
        solver.solve(available, list);
        solver = new DataflowSolver();
        solver.solve(earliest, list);
        solver = new DataflowSolver();
        solver.solve(postponed, list);
        solver = new DataflowSolver();
        solver.solve(latest, list);
        solver = new DataflowSolver();
        solver.solve(used, list);
        return transform(list);
    }
    class GetExpressions implements OperationVisitor {
        public void register(Operation op) {
            Expression e = new Expression(op);
            PartialRedundancy.this.opToExpression.put(op, e);
            allExpressions.add(e);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
         */
        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Join)
         */
        public Object visit(Join op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Project)
         */
        public Object visit(Project op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Rename)
         */
        public Object visit(Rename op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Union)
         */
        public Object visit(Union op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Difference)
         */
        public Object visit(Difference op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.JoinConstant)
         */
        public Object visit(JoinConstant op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.GenConstant)
         */
        public Object visit(GenConstant op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Free)
         */
        public Object visit(Free op) {
            //register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Universe)
         */
        public Object visit(Universe op) {
            //register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Zero)
         */
        public Object visit(Zero op) {
            //register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Invert)
         */
        public Object visit(Invert op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Copy)
         */
        public Object visit(Copy op) {
            //register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Load)
         */
        public Object visit(Load op) {
            //ignore, not intersting
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Save)
         */
        public Object visit(Save op) {
            //ingore, not intersting
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.ApplyEx)
         */
        public Object visit(ApplyEx op) {
            register(op);
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.If)
         */
        public Object visit(If op) {
            //ingore, shouldnt move
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.Nop)
         */
        public Object visit(Nop op) {
            //ignore, not intersting
            return null;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.Replace)
         */
        public Object visit(Replace op) {
            register(op);
            return null;
        }
    }
    public class Anticipated extends OperationProblem {
        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#direction()
         */
        public boolean direction() {
            return false;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
         */
        public Fact getBoundary() {
            return new AnticipatedFact();
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getTransferFunction(org.sf.bddbddb.ir.Operation)
         */
        public TransferFunction getTransferFunction(Operation o) {
            return new AnticipatedTF(o);
        }
        public class AnticipatedFact extends PreFact {
            public PreFact create() {
                return new AnticipatedFact();
            }

            /*
             * (non-Javadoc) perform set intersection
             * 
             * @see org.sf.bddbddb.dataflow.Problem.Fact#join(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact join(Fact that) {
                AnticipatedFact thatFact = (AnticipatedFact) that;
                AnticipatedFact result = new AnticipatedFact();
                result.loc = this.loc;
                result.expressions.addAll(this.expressions);
                result.expressions.retainAll(thatFact.expressions);
                return result;
            }

            public void killExpressions(Relation r) {
                if (r != null) for (Iterator it = expressions.iterator(); it.hasNext();) {
                    Expression e = (Expression) it.next();
                    if (e.uses(r)) it.remove();
                }
            }
        }
        class AnticipatedTF extends TransferFunction {
            Operation op;

            public AnticipatedTF(Operation op) {
                this.op = op;
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact apply(Fact f) {
                AnticipatedFact lastFact = (AnticipatedFact) f;
                //System.out.println(" lastFact: " + lastFact);
                AnticipatedFact currFact = (lastFact != null) ? (AnticipatedFact) lastFact.copy() : new AnticipatedFact();
                currFact.killExpressions(op.getRelationDest());
                currFact.addExpression((Expression) opToExpression.get(op));
                //System.out.println(" result : " + currFact);
                currFact.op = op;
                setFact(op, currFact);
                return currFact;
            }
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            SortedMap sortedMap = new TreeMap(new Comparator() {
                public int compare(Object o1, Object o2) {
                    return ((Operation) o1).id - ((Operation) o2).id;
                }
            });
            sortedMap.putAll(operationFacts);
            for (Iterator it = sortedMap.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                sb.append("@" + e.getKey() + " : " + e.getValue() + '\n');
            }
            return sb.toString();
        }
    }
    public class Available extends OperationProblem {
        public Map availOpIns;

        /**
         *  
         */
        public Available() {
            availOpIns = new HashMap();
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.OperationProblem#direction()
         */
        public boolean direction() {
            return true;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getTransferFunction(org.sf.bddbddb.ir.Operation)
         */
        public TransferFunction getTransferFunction(Operation o) {
            // TODO Auto-generated method stub
            return new AvailableTF(o);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
         */
        public Fact getBoundary() {
            return new AvailableFact();
        }
        public class AvailableFact extends PreFact {
            public PreFact create() {
                return new AvailableFact();
            }

            /*
             * perform intersection
             * 
             * @see org.sf.bddbddb.dataflow.Problem.Fact#join(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact join(Fact that) {
                AvailableFact result = new AvailableFact();
                AvailableFact thatFact = (AvailableFact) that;
                result.expressions.addAll(this.expressions);
                result.expressions.retainAll(thatFact.expressions);
                result.loc = this.loc;
                return result;
            }

            public void killExpressions(Relation r) {
                for (Iterator it = expressions.iterator(); it.hasNext();) {
                    Expression e = (Expression) it.next();
                    if (e.uses(r)) it.remove();
                }
            }
        }
        class AvailableTF extends TransferFunction {
            Operation op;

            public AvailableTF(Operation op) {
                this.op = op;
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact apply(Fact f) {
                AvailableFact lastFact = (AvailableFact) f;
                setIn(op, lastFact);
                AvailableFact currFact = (lastFact) != null ? (AvailableFact) lastFact.copy() : new AvailableFact();
                AnticipatedFact antiFact = (AnticipatedFact) anticipated.getFact(op);
                currFact.addExpressions(antiFact.getExpressions());
                currFact.killExpressions(op.getRelationDest());
                currFact.op = op;
                setFact(op, currFact);
                return currFact;
            }
        }

        private void setIn(Operation op, AvailableFact lastFact) {
            availOpIns.put(op, lastFact);
        }

        public AvailableFact getIn(Operation op) {
            return (AvailableFact) availOpIns.get(op);
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            SortedMap sortedMap = new TreeMap(new Comparator() {
                public int compare(Object o1, Object o2) {
                    return ((Operation) o1).id - ((Operation) o2).id;
                }
            });
            sortedMap.putAll(operationFacts);
            for (Iterator it = sortedMap.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                sb.append("@" + e.getKey() + " : " + e.getValue() + '\n');
            }
            return sb.toString();
        }
    }
    public class Earliest extends OperationProblem {
        public boolean direction() {
            return true;
        }

        public TransferFunction getTransferFunction(Operation o) {
            return new EarliestTF(o);
        }

        public Fact getBoundary() {
            return new EarliestFact();
        }
        public class EarliestTF extends TransferFunction {
            Operation op;

            /**
             * @param op
             */
            public EarliestTF(Operation op) {
                super();
                this.op = op;
            }

            public Fact apply(Fact f) {
                EarliestFact lastFact = (EarliestFact) f;
                AnticipatedFact antiFact = (AnticipatedFact) anticipated.getFact(op);
                AvailableFact availFact = available.getIn(op);
                EarliestFact currFact = new EarliestFact();
                currFact.addExpressions(antiFact.getExpressions());
                if (availFact != null) currFact.removeExpressions(availFact.getExpressions());
                //currFact.removeExpression((Expression)
                // opToExpression.get(op));
                currFact.op = op;
                setFact(op, currFact);
                return currFact;
            }
        }
        public class EarliestFact extends PreFact {
            public PreFact create() {
                return new EarliestFact();
            }

            public Fact join(Fact that) {
                return this;
            }
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            SortedMap sortedMap = new TreeMap(new Comparator() {
                public int compare(Object o1, Object o2) {
                    return ((Operation) o1).id - ((Operation) o2).id;
                }
            });
            sortedMap.putAll(operationFacts);
            for (Iterator it = sortedMap.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                sb.append("@" + e.getKey() + " : " + e.getValue() + '\n');
            }
            return sb.toString();
        }
    }
    public class Postponed extends OperationProblem {
        Map opIns;

        /**
         *  
         */
        public Postponed() {
            super();
            opIns = new HashMap();
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.OperationProblem#direction()
         */
        public boolean direction() {
            return true;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getTransferFunction(org.sf.bddbddb.ir.Operation)
         */
        public TransferFunction getTransferFunction(Operation o) {
            return new PostponedTF(o);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
         */
        public Fact getBoundary() {
            return new PostponedFact();
        }
        class PostponedTF extends TransferFunction {
            Operation op;

            /**
             * @param op
             */
            public PostponedTF(Operation op) {
                super();
                this.op = op;
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact apply(Fact f) {
                PostponedFact lastFact = (PostponedFact) f;
                setIn(op, lastFact);
                EarliestFact earlFact = (EarliestFact) earliest.getFact(op);
                PostponedFact newFact = (PostponedFact) lastFact.copy();
                newFact.addExpressions(earlFact.expressions);
                newFact.removeExpression((Expression) opToExpression.get(op));
                newFact.op = op;
                setFact(op, newFact);
                return newFact;
            }
        }
        public class PostponedFact extends PreFact {
            public Fact join(Fact that) {
                PostponedFact thatFact = (PostponedFact) that;
                PostponedFact result = new PostponedFact();
                result.expressions.addAll(this.expressions);
                result.expressions.retainAll(thatFact.expressions);
                result.loc = this.loc;
                return result;
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.PartialRedundancy.PreFact#create()
             */
            public PreFact create() {
                return new PostponedFact();
            }
        }

        public void setIn(Operation op, PostponedFact fact) {
            opIns.put(op, fact);
        }

        public PostponedFact getIn(Operation op) {
            return (PostponedFact) opIns.get(op);
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            SortedMap sortedMap = new TreeMap(new Comparator() {
                public int compare(Object o1, Object o2) {
                    return ((Operation) o1).id - ((Operation) o2).id;
                }
            });
            sortedMap.putAll(operationFacts);
            for (Iterator it = sortedMap.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                sb.append("@" + e.getKey() + " : " + e.getValue() + '\n');
            }
            return sb.toString();
        }
    }
    public class Latest extends OperationProblem {
        /**
         * @author Administrator
         * 
         * TODO To change the template for this generated type comment go to
         * Window - Preferences - Java - Code Style - Code Templates
         */
        public class LatestTF extends TransferFunction {
            Operation op;

            /**
             * @param op
             */
            public LatestTF(Operation op) {
                super();
                this.op = op;
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact apply(Fact f) {
                LatestFact lastFact = (LatestFact) f;
                Set right = new HashSet(lastFact.expressions);
                Set trueRight = new HashSet(allExpressions);
                trueRight.removeAll(right);
                trueRight.add(opToExpression.get(op));
                Set left = new HashSet(((EarliestFact) earliest.getFact(op)).expressions);
                left.addAll(postponed.getIn(op).expressions);
                LatestFact returnLeft = new LatestFact();
                returnLeft.addExpressions(left);
                left.retainAll(trueRight);
                LatestFact thisLatest = new LatestFact();
                thisLatest.addExpressions(left);
                thisLatest.op = op;
                setFact(op, thisLatest);
                return returnLeft;
            }
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.OperationProblem#direction()
         */
        public boolean direction() {
            return false;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getTransferFunction(org.sf.bddbddb.ir.Operation)
         */
        public TransferFunction getTransferFunction(Operation o) {
            return new LatestTF(o);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
         */
        public Fact getBoundary() {
            // TODO Auto-generated method stub
            return new LatestFact();
        }
        public class LatestFact extends PreFact {
            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.PartialRedundancy.PreFact#create()
             */
            public PreFact create() {
                return new LatestFact();
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.Problem.Fact#join(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact join(Fact that) {
                LatestFact thatFact = (LatestFact) that;
                LatestFact result = new LatestFact();
                result.expressions.addAll(this.expressions);
                result.expressions.retainAll(thatFact.expressions);
                result.loc = this.loc;
                return result;
            }
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            SortedMap sortedMap = new TreeMap(new Comparator() {
                public int compare(Object o1, Object o2) {
                    return ((Operation) o1).id - ((Operation) o2).id;
                }
            });
            sortedMap.putAll(operationFacts);
            for (Iterator it = sortedMap.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                sb.append("@" + e.getKey() + " : " + e.getValue() + '\n');
            }
            return sb.toString();
        }
    }
    public class Used extends OperationProblem {
        public HashMap opOuts;

        /**
         *  
         */
        public Used() {
            opOuts = new HashMap();
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.OperationProblem#direction()
         */
        public boolean direction() {
            return false;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getTransferFunction(org.sf.bddbddb.ir.Operation)
         */
        public TransferFunction getTransferFunction(Operation o) {
            return new UsedTF(o);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
         */
        public Fact getBoundary() {
            return new UsedFact();
        }
        public class UsedFact extends PreFact {
            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.PartialRedundancy.PreFact#create()
             */
            public PreFact create() {
                return new UsedFact();
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.Problem.Fact#join(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact join(Fact that) {
                UsedFact thatFact = (UsedFact) that;
                UsedFact result = (UsedFact) create();
                result.addExpressions(this.expressions);
                result.addExpressions(thatFact.expressions);
                result.loc = this.loc;
                return result;
            }

            public void killExpressions(Relation r) {
                for (Iterator it = expressions.iterator(); it.hasNext();) {
                    Expression e = (Expression) it.next();
                    if (e.uses(r)) it.remove();
                }
            }
        }
        public class UsedTF extends TransferFunction {
            Operation op;

            /**
             * @param op
             */
            public UsedTF(Operation op) {
                super();
                this.op = op;
            }

            /*
             * (non-Javadoc)
             * 
             * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
             */
            public Fact apply(Fact f) {
                UsedFact lastFact = (UsedFact) f;
                setOut(op, lastFact);
                UsedFact newFact = new UsedFact();
                newFact.addExpressions(lastFact.expressions);
                newFact.killExpressions(op.getRelationDest());
                newFact.addExpression((Expression) opToExpression.get(op));
                newFact.removeExpressions(((EarliestFact) earliest.getFact(op)).expressions);
                newFact.op = op;
                setFact(op, newFact);
                return newFact;
            }
        }

        public void setOut(Operation op, UsedFact fact) {
            opOuts.put(op, fact);
        }

        public UsedFact getOut(Operation op) {
            return (UsedFact) opOuts.get(op);
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            SortedMap sortedMap = new TreeMap(new Comparator() {
                public int compare(Object o1, Object o2) {
                    return ((Operation) o1).id - ((Operation) o2).id;
                }
            });
            sortedMap.putAll(operationFacts);
            for (Iterator it = sortedMap.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                sb.append("@" + e.getKey() + " : " + e.getValue() + '\n');
            }
            return sb.toString();
        }
    }
    Map exprToOp = new HashMap();

    public boolean transform(IterationList list) {
        boolean changed = false;
        if (list.isLoop()) {
            boolean b = transform(list.getLoopEdge());
            if (!changed) changed = b; //check not needed. here in case of move
        }
        for (ListIterator it = list.iterator(); it.hasNext();) {
            Object o = it.next();
            if (o instanceof Operation) {
                /*
                 * System.out.println("Analyzing Operation: " + o);
                 * System.out.println(" earliest: " +
                 * earliest.getFact((Operation) o)); System.out.println(" used: " +
                 * used.getOut((Operation) o ));
                 */
                Set latest = ((LatestFact) PartialRedundancy.this.latest.getFact((Operation) o)).expressions;
                latest.retainAll(used.getOut(((Operation) o)).expressions);
                //System.out.println(" adding ops for: " + latest);
                it.previous();
                for (Iterator it2 = latest.iterator(); it2.hasNext();) {
                    Expression e = (Expression) it2.next();
                    Operation relOp = (Operation) exprToOp.get(e);
                    if (relOp == null) {
                        Relation oldR = e.op.getRelationDest();
                        if (oldR != null) {
                            Relation r = solver.createRelation("pre_" + e.toString(), oldR.getAttributes());
                            r.initialize();
                            relOp = e.op.copy();
                            relOp.setRelationDest(r);
                            exprToOp.put(e, relOp);
                        }
                    }
                    if (TRACE) System.out.println("Adding " + relOp + " before " + o);
                    it.add(relOp);
                    changed = true;
                }
                it.next();
                Set notLatest = new HashSet(allExpressions);
                notLatest.removeAll(((LatestFact) PartialRedundancy.this.latest.getFact((Operation) o)).expressions);
                notLatest.addAll(used.getOut((Operation) o).expressions);
                if (notLatest.contains(opToExpression.get(o))) {
                    Expression e = (Expression) opToExpression.get(o);
                    Operation op = (Operation) exprToOp.get(e);
                    if (e != null && op != null) {
                        Copy newOp = new Copy(((Operation) o).getRelationDest(), op.getRelationDest());
                        if (TRACE) System.out.println("Replacing " + o + " with " + newOp);
                        it.set(newOp);
                        changed = true;
                    }
                }
                if (o instanceof Nop) it.remove(); //remove nops
            } else {
                IterationList l = (IterationList) o;
                boolean b = transform(l);
                if (!changed) changed = b;
                //clean up empty lists
                if (l.isEmpty()) it.remove();
            }
        }
        return changed;
    }
    abstract class PreFact implements OperationFact {
        Operation op;
        IterationList loc;
        public Set expressions;

        public PreFact() {
            expressions = new HashSet();
        }

        public boolean containsExpression(Expression e) {
            return expressions.contains(e);
        }

        public boolean addExpression(Expression e) {
            if (e != null) return expressions.add(e);
            return false;
        }

        public boolean addExpressions(Set e) {
            return expressions.addAll(e);
        }

        public boolean removeExpression(Expression e) {
            return expressions.remove(e);
        }

        public boolean removeExpressions(Set e) {
            return expressions.removeAll(e);
        }

        public Set getExpressions() {
            return expressions;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#copy(org.sf.bddbddb.IterationList)
         */
        public Fact copy(IterationList list) {
            PreFact result = this.copy();
            result.loc = list;
            return result;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#setLocation(org.sf.bddbddb.IterationList)
         */
        public void setLocation(IterationList list) {
            loc = list;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#getLocation()
         */
        public IterationList getLocation() {
            return loc;
        }

        public String toString() {
            return expressions.toString();
        }

        public boolean equals(Object o) {
            return expressions.equals(((PreFact) o).expressions);
        }

        public abstract PreFact create();

        public PreFact copy() {
            PreFact result = create();
            result.expressions.addAll(this.expressions);
            result.loc = loc;
            return result;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.OperationProblem.OperationFact#getOperation()
         */
        public Operation getOperation() {
            return op;
        }
    }
    class Expression {
        Operation op;

        public Expression(Operation op) {
            this.op = op;
        }

        public List getSrcs() {
            return op.getSrcs();
        }

        public Class getType() {
            return op.getClass();
        }

        public boolean equals(Object o) {
            if (this == o) return true;
            if (o instanceof Expression) {
                Expression that = (Expression) o;
                if (!this.op.getExpressionString().equals(that.op.getExpressionString())) return false;
                return true;
            }
            return false;
        }

        public boolean uses(Relation r) {
            return getSrcs().contains(r);
        }

        public String toString() {
            return op.getExpressionString();
        }

        public int hashCode() {
            return op.getExpressionString().hashCode();
        }
    }
    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.dataflow.IRPass#run()
     */
}