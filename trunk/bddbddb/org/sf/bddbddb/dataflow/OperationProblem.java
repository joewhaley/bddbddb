// RelationProblem.java, created Jul 3, 2004 1:44:46 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.dataflow;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.ir.Operation;

/**
 * RelationProblem
 * 
 * @author John Whaley
 * @version $Id$
 */
public abstract class OperationProblem extends Problem {
    public abstract boolean direction();

    public abstract static class OperationFacts implements Fact {
        Map/* <Operation,OperationFact> */operationFacts;

        IterationList location;

        Operation lastOp;

        public abstract OperationFacts create();

        public OperationFacts() {
            initialize();
        }

        public void initialize() {
            operationFacts = new HashMap();
        }

        public OperationFact getFact(Operation o) {
            return (OperationFact) operationFacts.get(o);
        }

        public int hashCode() {
            return operationFacts.hashCode();
        }

        public boolean equals(Object o) {
            OperationFacts that = (OperationFacts) o;
            if (this.operationFacts == that.operationFacts) return true;
            if (operationFacts.size() != that.operationFacts.size()) {
                System.out.println("Size not equal");
                return false;
            }
            Iterator i = operationFacts.entrySet().iterator();
            while (i.hasNext()) {
                Map.Entry e = (Map.Entry) i.next();
                Object key = e.getKey();
                Object value = e.getValue();
                Object value2 = that.operationFacts.get(key);
                if (!value.equals(value2)) {
                    System.out.println("Key " + key + " differs: " + value
                        + " vs " + value2);
                    return false;
                }
            }
            return true;
        }

        public void setLocation(IterationList loc) {
            this.location = loc;
        }

        public IterationList getLocation() {
            return location;
        }

        public Fact join(Fact fact) {
            OperationFacts that = (OperationFacts) fact;
            OperationFacts result = (OperationFacts) create();
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
            OperationFact thisLastFact = (OperationFact) getLastFact();
            OperationFact thatLastFact = (OperationFact) that.getLastFact();
            if (thisLastFact != null) {
                OperationFact resultLastFact = (OperationFact) thisLastFact
                    .join(thatLastFact);
                ;

                result.setLastOp(that.lastOp);
                result.setLastFact(resultLastFact);
            }
            result.location = location;
            return result;
        }

        public OperationFact getLastFact() {
            if (lastOp != null) return getFact(lastOp);
            return null;
        }

        public void setLastOp(Operation op) {
            lastOp = op;
        }

        public void setLastFact(OperationFact fact) {
            operationFacts.put(lastOp, fact);
        }
    }

    public static abstract interface OperationFact extends Fact {
    }
}