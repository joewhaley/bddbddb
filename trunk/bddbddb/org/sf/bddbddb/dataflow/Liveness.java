package org.sf.bddbddb.dataflow;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.IR;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.util.BitString;

/**
 * @author Administrator
 */
public class Liveness extends OperationProblem {
    public IR ir;

    public LivenessFacts currentFacts;

    IterationList currentLocation;

    Operation lastOp;

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
        return new LivenessFacts();
    }

    public class LivenessFacts extends OperationFacts {
        public OperationFacts create() {
            return new LivenessFacts();
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            for (Iterator it = operationFacts.entrySet().iterator(); it
                .hasNext();) {
                Map.Entry e = (Map.Entry) it.next();
                Object key = e.getKey();
                Object value = e.getValue();
                sb.append(key + ": " + value);
                sb.append('\n');
            }
            return sb.toString();
        }
    }

    public class LivenessFact extends UnionBitVectorFact implements
        OperationFact {
        public LivenessFact(BitString fact) {
            super(fact);
        }

        public LivenessFact(int size) {
            super(size);
        }

        public Fact join(Fact that) {
            return new LivenessFact(
                ((UnionBitVectorFact) super.join(that)).fact);
        }

        public String toString() {
            Integer one = new Integer(1);
            StringBuffer sb = new StringBuffer();
            for (int i = 0; i < fact.size(); i++) {
                if (fact.get(i)) {
                    sb.append(ir.getRelation(i));
                    sb.append(" ");
                }
            }
            return sb.toString();
        }

        public boolean isAlive(Relation r) {
            return fact.get(r.id);
        }
    }

    public TransferFunction getTransferFunction(Operation op) {
        return new LivenessTF(op);
    }

    public class LivenessTF extends TransferFunction {
        Operation op;

        LivenessFact lastFact;

        LivenessFact currFact;

        public LivenessTF(Operation op) {
            this.op = op;
        }

        public Fact apply(Fact f) {
            currentFacts = (LivenessFacts) f;
            lastFact = (LivenessFact) currentFacts.getLastFact();
            currFact = (LivenessFact) currentFacts.getFact(op);
            LivenessFact newFact = new LivenessFact(numRelations);
            if (lastFact != null) newFact.fact.copyBits(lastFact.fact);
            //kill
            Relation r = op.getRelationDest();
            if (r != null) newFact.fact.clear(r.id);
            //gen
            List srcs = op.getSrcs();
            for (Iterator it = srcs.iterator(); it.hasNext();) {
                Object o = it.next();
                if (o instanceof Relation) newFact.fact.set(((Relation) o).id);
            }
            currentFacts.operationFacts.put(op, newFact);
            currentFacts.setLastFact(newFact);
            return currentFacts;
        }
    }
}