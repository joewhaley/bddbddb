// DefUse.java, created Jul 3, 2004 9:53:25 PM by jwhaley
//Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
//Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.dataflow;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.IR;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.util.BitString;
import org.sf.bddbddb.util.BitString.BitStringIterator;

/**
 * DefUse
 * 
 * @author jwhaley
 * @version $Id$
 */
public class DefUse extends OperationProblem {

    // Global information.
    BitString[] defs; /* <Relation,Operation> */

    BitString[] uses; /* <Relation,Operation> */

    Operation[] opMap;

    IR ir;

    public DefUse(IR ir) {
        this.ir = ir;
        int numRelations = ir.getNumberOfRelations();
        int numOperations = Operation.getNumberOfOperations();
        this.defs = new BitString[numRelations];
        for (int i = 0; i < defs.length; ++i) {
            defs[i] = new BitString(numOperations);
        }
        this.uses = new BitString[numRelations];
        for (int i = 0; i < uses.length; ++i) {
            uses[i] = new BitString(numOperations);
        }
        opMap = new Operation[numOperations];
        initialize(ir.graph.getIterationList());
    }

    void initialize(IterationList block) {
        for (Iterator i = block.iterator(); i.hasNext();) {
            Object o = i.next();
            if (o instanceof IterationList) initialize((IterationList) block);
            else {
                Operation op = (Operation) o;
                opMap[op.id] = op;
                Relation def = op.getRelationDest();
                defs[def.id].set(op.id);
                Collection use = op.getSrcs();
                for (Iterator j = use.iterator(); j.hasNext();) {
                    Relation r = (Relation) j.next();
                    uses[r.id].set(op.id);
                }
            }
        }
    }

    public OperationSet getDefs(Relation r) {
        return new OperationSet(defs[r.id]);
    }

    public OperationSet getUses(Relation r) {
        return new OperationSet(uses[r.id]);
    }

    public class OperationSet extends AbstractSet {

        BitString s;

        public OperationSet(BitString s) {
            this.s = s;
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.AbstractCollection#iterator()
         */
        public Iterator iterator() {
            return new OperationIterator(s);
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.Collection#contains(java.lang.Object)
         */
        public boolean contains(Object o) {
            if (o instanceof Operation) {
                int id = ((Operation) o).id;
                return s.get(id);
            }
            return false;
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.AbstractCollection#size()
         */
        public int size() {
            return s.numberOfOnes();
        }

    }

    public class OperationIterator implements Iterator {

        BitStringIterator i;

        public OperationIterator(BitString s) {
            i = s.iterator();
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.Iterator#hasNext()
         */
        public boolean hasNext() {
            return i.hasNext();
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.Iterator#next()
         */
        public Object next() {
            int index = i.nextIndex();
            return opMap[index];
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.Iterator#remove()
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

    public class DefUseFact extends UnionBitVectorFact implements OperationFact {

        IterationList location;

        DefUseFact(int setSize) {
            super(setSize);
        }

        DefUseFact(BitString s) {
            super(s);
        }

        public Fact join(Fact that) {
            return new DefUseFact(((UnionBitVectorFact) super.join(that)).fact);
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

        public OperationSet getDefs(Relation r) {
            return new OperationSet(fact);
        }
    }

    public boolean direction() {
        return true;
    }

    public TransferFunction getTransferFunction(Operation op) {
        return new DefUseTransferFunction(op);
    }

    public class DefUseFacts extends OperationFacts {
        public OperationFacts create() {
            return new DefUseFacts();
        }

        public Fact copy(IterationList loc) {
            DefUseFacts that = new DefUseFacts();
            that.operationFacts.putAll(this.operationFacts);
            that.location = loc;
            return that;
        }

        public Fact join(Fact fact) {
            DefUseFacts that = (DefUseFacts) fact;
            DefUseFacts result = (DefUseFacts) create();
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
            DefUseFact thisLastFact = (DefUseFact) getLastFact();
            DefUseFact thatLastFact = (DefUseFact) that.getLastFact();
            if (thisLastFact != null) {
                DefUseFact resultLastFact = (DefUseFact) thisLastFact
                    .join(thatLastFact);
                // resultLastFact.fact.or(thisLastFact.fact);
                //resultLastFact.fact.or(thatLastFact.fact);

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
                return false;
            }
            Iterator i = operationFacts.entrySet().iterator();
            while (i.hasNext()) {
                Map.Entry e = (Map.Entry) i.next();
                Object key = e.getKey();
                Object value = e.getValue();
                Object value2 = that.operationFacts.get(key);
                if (!value.equals(value2)) {
                    return false;
                }
            }
            return true;
        }
    }

    public class DefUseTransferFunction extends TransferFunction {

        Operation op;

        DefUseTransferFunction(Operation op) {
            this.op = op;
        }

        public Fact apply(Fact f) {
            DefUseFacts currentFacts;
            DefUseFact lastFact, currFact;
            currentFacts = (DefUseFacts) f;
            lastFact = (DefUseFact) currentFacts.getLastFact();
            currFact = (DefUseFact) currentFacts.getFact(op);
            DefUseFact newFact = new DefUseFact(ir.getNumberOfRelations());
            if (lastFact != null) newFact.fact.copyBits(lastFact.fact);
            //kill
            Relation r = op.getRelationDest();
            if (r != null) newFact.fact.minus(defs[r.id]);
            //gen
            newFact.fact.set(op.id);
            currentFacts.operationFacts.put(op, newFact);
            //currentFacts.setLastOp(op);
            currentFacts.setLastFact(newFact);
            return currentFacts;
        }

    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.dataflow.Problem#getBoundary()
     */
    public Fact getBoundary() {
        return new DefUseFacts();
    }
}