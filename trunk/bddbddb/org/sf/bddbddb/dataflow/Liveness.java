package org.sf.bddbddb.dataflow;

import java.util.Iterator;
import java.util.List;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.IR;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.util.BitString;
import org.sf.bddbddb.util.BitString.BitStringIterator;

/**
 * @author Administrator
 */
public class Liveness extends OperationProblem {
    public IR ir;

    int numRelations;

    boolean TRACE = false;

    public Liveness(IR ir) {
        this.ir = ir;
        this.numRelations = ir.getNumberOfRelations();
    }

    public boolean direction() {
        return false;
    }

    public Fact getBoundary() {
        return new LivenessFact(numRelations);
    }

    public class LivenessFact extends UnionBitVectorFact implements OperationFact {
        
        Operation op;
        
        public LivenessFact(BitString fact) {
            super(fact);
        }
        
        public LivenessFact(int size) {
            super(size);
        }
        
        public UnionBitVectorFact create(BitString bs) {
            return new LivenessFact(bs);
        }
        
        public Fact join(Fact that) {
            if (TRACE) System.out.println("Joining "+this+" and "+that);
            Fact result = super.join(that);
            if (TRACE) System.out.println("Result = "+result);
            return result;
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         */
        public String toString() {
            StringBuffer sb = new StringBuffer();
            sb.append(op);
            sb.append(" : ");
            for (BitStringIterator i = fact.iterator(); i.hasNext(); ) {
                sb.append(ir.getRelation(i.nextIndex()));
                sb.append(" ");
            }
            return sb.toString();
        }

        public boolean isAlive(Relation r) {
            return fact.get(r.id);
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.dataflow.OperationProblem.OperationFact#getOperation()
         */
        public Operation getOperation() {
            return op;
        }
        
        public void setLocation(IterationList list) {
        }
        
        public Fact copy(IterationList list) {
            return create(fact);
        }
    }

    public TransferFunction getTransferFunction(Operation op) {
        return new LivenessTF(op);
    }

    public class LivenessTF extends OperationTransferFunction {
        Operation op;

        public LivenessTF(Operation op) {
            this.op = op;
        }

        public Fact apply(Fact f) {
            //super.apply(f);
            LivenessFact oldFact = (LivenessFact) f;
            BitString bs = (BitString) oldFact.fact.clone();
            //kill
            Relation r = op.getRelationDest();
            if (r != null) bs.clear(r.id);
            //gen
            List srcs = op.getSrcs();
            for (Iterator it = srcs.iterator(); it.hasNext();) {
                Object o = it.next();
                if (o instanceof Relation) bs.set(((Relation) o).id);
            }
            LivenessFact newFact = (LivenessFact) oldFact.create(bs);
            newFact.op = op;
            setFact(op, newFact);
            return newFact;
        }
    }
}