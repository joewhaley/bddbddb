/*
 * Created on Jul 10, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.dataflow;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
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
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class CopyProp extends OperationProblem implements IRPass {
    /**
     * @author mcarbin
     * 
     * TODO To change the template for this generated type comment go to Window -
     * Preferences - Java - Code Style - Code Templates
     */
    IR ir;
    Map opIns;
    boolean TRACE = false;

    public CopyProp(IR ir) {
        this.ir = ir;
        opIns = new HashMap();
    }

    public boolean run() {
        IterationList list = ir.graph.getIterationList();
        DataflowSolver df_solver = new DataflowSolver();
        df_solver.solve(this, list);
        return transform(list);
    }

    public void setIn(Operation op, CopyPropFact fact) {
        opIns.put(op, fact);
    }

    public CopyPropFact getIn(Operation op) {
        return (CopyPropFact) opIns.get(op);
    }
    public class CopyPropFact implements OperationFact {
        Operation op;
        Map copies;
        IterationList loc;

        //MultiMap reverseCopies;
        public CopyPropFact() {
            copies = new HashMap();
            //reverseCopies = new GenericMultiMap();
        }

        public Relation getCopy(Relation r) {
            return (Relation) copies.get(r);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.OperationProblem.OperationFact#getOperation()
         */
        public Operation getOperation() {
            return op;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#join(org.sf.bddbddb.dataflow.Problem.Fact)
         */
        public Fact join(Fact that) {
            CopyPropFact thatFact = (CopyPropFact) that;
            CopyPropFact result = new CopyPropFact();
            result.copies.putAll(this.copies);
            Map thatCopies = thatFact.copies;
            for (Iterator it = this.copies.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                Relation thisKey = (Relation) e.getKey();
                Relation thisValue = (Relation) e.getValue();
                Relation thatValue = (Relation) thatCopies.get(thisKey);
                if (thatValue == null) {
                    result.copies.remove(thisKey);
                } else {
                    if (!thisValue.equals(thatValue)) result.copies.remove(thisKey);
                }
            }
            result.loc = this.loc;
            return result;
        }

        public CopyPropFact copy() {
            CopyPropFact result = new CopyPropFact();
            result.copies.putAll(this.copies);
            result.op = this.op;
            result.loc = this.loc;
            return result;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#copy(org.sf.bddbddb.IterationList)
         */
        public Fact copy(IterationList loc) {
            CopyPropFact c = copy();
            c.loc = loc;
            return c;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#setLocation(org.sf.bddbddb.IterationList)
         */
        public void setLocation(IterationList loc) {
            this.loc = loc;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#getLocation()
         */
        public IterationList getLocation() {
            return loc;
        }

        public boolean equals(Object o) {
            if (o instanceof CopyPropFact) {
                return this.copies.equals(((CopyPropFact) o).copies);
            }
            return false;
        }

        public String toString() {
            return copies.toString();
        }
    }
    /**
     * @author Administrator
     * 
     * TODO To change the template for this generated type comment go to Window -
     * Preferences - Java - Code Style - Code Templates
     */
    public class CopyPropTF extends TransferFunction {
        Operation op;

        /**
         * @param op
         */
        public CopyPropTF(Operation op) {
            super();
            this.op = op;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
         */
        public Fact apply(Fact f) {
            CopyPropFact lastFact = (CopyPropFact) f;
            setIn(op, lastFact);
            CopyPropFact newFact = lastFact.copy();
            Relation dest = op.getRelationDest();
            for (Iterator it = newFact.copies.entrySet().iterator(); it.hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                Relation key = (Relation) e.getKey();
                Relation value = (Relation) e.getValue();
                if (key.equals(dest) || value.equals(dest)) it.remove();
            }
            if (op instanceof Copy) {
                Copy cOp = (Copy) op;
                Relation src = cOp.getSrc();
                newFact.copies.put(cOp.getRelationDest(), src);
            }
            newFact.op = op;
            setFact(op, newFact);
            return newFact;
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.dataflow.Problem#direction()
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
        return new CopyPropTF(o);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
     */
    public Fact getBoundary() {
        return new CopyPropFact();
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

    public boolean transform(IterationList list) {
        boolean changed = false;
        for (Iterator it = list.iterator(); it.hasNext();) {
            Object o = it.next();
            if (o instanceof Operation) {
                Boolean b = (Boolean) ((Operation) o).visit(new Transformer());
                if (!changed) changed = b.booleanValue();
            } else {
                boolean b = transform((IterationList) o);
                if (!changed) changed = b;
            }
        }
        if (list.isLoop()) {
            boolean b = transform(list.getLoopEdge());
            if (!changed) changed = b;
        }
        return changed;
    }
    class Transformer implements OperationVisitor {
        
        public Object visitBinary(Operation op, Relation src1, Relation src2){
            Boolean changed = Boolean.FALSE;
            CopyPropFact fact = getIn(op);
            Relation t1 = fact.getCopy(src1);
            if (t1 != null && !t1.equals(src1)) {
                if (TRACE) System.out.println(op + ": replacing " + src1 + " with " + t1);
                op.replaceSrc(src1, t1);
                changed = Boolean.TRUE;
            }
            Relation t2 = fact.getCopy(src2);
            if (t2 != null && !t2.equals(src2)) {
                if (TRACE) System.out.println(op + ": changing " + src2 + " to " + t2);
                op.replaceSrc(src2, t2);
                changed = Boolean.TRUE;
            }
            return changed;
        }
        public Object visitUnary(Operation op, Relation src){
            CopyPropFact fact = getIn(op);
            Relation t = fact.getCopy(src);
            if (t != null && !t.equals(src)) {
                if (TRACE) System.out.println(op + ": changing " + src + " to " + t);
                op.replaceSrc(src, t);
                return Boolean.TRUE;
            }
            return Boolean.FALSE;
        }
        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Join)
         */
        public Object visit(Join op) {
            Boolean changed = Boolean.FALSE;
            Relation src1 = op.getSrc1();
            Relation src2 = op.getSrc2();
            return visitBinary(op,src1,src2);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Project)
         */
        public Object visit(Project op) {
            Relation src = op.getSrc();
            return visitUnary(op,src);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Rename)
         */
        public Object visit(Rename op) {
            Relation src = op.getSrc();
            return visitUnary(op,src);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Union)
         */
        public Object visit(Union op) {
            
            Relation src1 = op.getSrc1();
            Relation src2 = op.getSrc2();
            return visitBinary(op,src1,src2);
           
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Difference)
         */
        public Object visit(Difference op) {
            Relation src1 = op.getSrc1();
            Relation src2 = op.getSrc2();
            return visitBinary(op,src1,src2);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.JoinConstant)
         */
        public Object visit(JoinConstant op) {
            Relation src = op.getSrc();
            return visitUnary(op,src);
           }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.GenConstant)
         */
        public Object visit(GenConstant op) {
            return Boolean.FALSE;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Free)
         */
        public Object visit(Free op) {
            Relation src = op.getSrc();
           return visitUnary(op,src);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Universe)
         */
        public Object visit(Universe op) {
            return Boolean.FALSE;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Zero)
         */
        public Object visit(Zero op) {
            return Boolean.FALSE;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Invert)
         */
        public Object visit(Invert op) {
            Relation src = op.getSrc();
            return visitUnary(op,src);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Copy)
         */
        public Object visit(Copy op) {
            Relation src = op.getSrc();
           return visitUnary(op,src);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Load)
         */
        public Object visit(Load op) {
            return Boolean.FALSE;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Save)
         */
        public Object visit(Save op) {
            Relation src = op.getSrc();
            return visitUnary(op,src);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.ApplyEx)
         */
        public Object visit(ApplyEx op) {
            Relation src1 = op.getSrc1();
            Relation src2 = op.getSrc2();
            return visitBinary(op,src1,src2);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.If)
         */
        public Object visit(If op) {
            return Boolean.FALSE;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.Nop)
         */
        public Object visit(Nop op) {
            return Boolean.FALSE;
        }

        public Object visit(Replace op) {
            Relation src = op.getSrc();
            return visitUnary(op,src);
        }
       
    
    }
    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.dataflow.IRPass#run()
     */
}