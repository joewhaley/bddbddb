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

        public Fact copy(IterationList loc) {
            LivenessFacts that = new LivenessFacts();
            that.operationFacts.putAll(this.operationFacts);
            that.location = loc;
            that.lastOp = lastOp;
            return that;
        }

        public Fact join(Fact fact) {
            LivenessFacts that = (LivenessFacts) fact;
            LivenessFacts result = (LivenessFacts) create();
            result.operationFacts.putAll(this.operationFacts);
            for (Iterator i = that.operationFacts.entrySet().iterator(); i
                .hasNext();) {
                Map.Entry e = (Map.Entry) i.next();
                Operation o = (Operation) e.getKey();
                OperationFact f = (OperationFact) e.getValue();
                OperationFact old = (OperationFact) result.operationFacts.put(
                    o, f);
                if (old != null) {
                    f = (OperationFact) f.join(old);
                    result.operationFacts.put(o, f);
                }
            }
            LivenessFact thisLastFact = (LivenessFact) getLastFact();
            LivenessFact thatLastFact = (LivenessFact) that.getLastFact();
            if (thisLastFact != null) {
                LivenessFact resultLastFact = (LivenessFact) thisLastFact
                    .join(thatLastFact);
                ;
                // resultLastFact.fact.or(thisLastFact.fact);
                //resultLastFact.fact.or(thatLastFact.fact);

                result.setLastOp(that.lastOp);
                result.setLastFact(resultLastFact);
            }
            result.location = location;
            return result;
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

        public boolean equals(Object o) {
            OperationFacts that = (OperationFacts) o;
            if (this.operationFacts == that.operationFacts) return true;
            if (operationFacts.size() != that.operationFacts.size()) {
                if (TRACE) System.out.println("Size not equal");
                return false;
            }
            Iterator i = operationFacts.entrySet().iterator();
            while (i.hasNext()) {
                Map.Entry e = (Map.Entry) i.next();
                Object key = e.getKey();
                Object value = e.getValue();
                Object value2 = that.operationFacts.get(key);
                if (!value.equals(value2)) {
                    if (TRACE) System.out.println("Key " + key + " differs: "
                        + value + " vs " + value2);
                    return false;
                }
            }
            return true;
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
                newFact.fact.set(((Relation) it.next()).id);
            }
            currentFacts.operationFacts.put(op, newFact);
            currentFacts.setLastOp(op);
            return currentFacts;
        }
    }
}