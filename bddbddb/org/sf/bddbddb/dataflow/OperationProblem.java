// RelationProblem.java, created Jul 3, 2004 1:44:46 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.dataflow;

import java.util.HashMap;
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

        public boolean equals(OperationFacts that) {
            return operationFacts.equals(that.operationFacts);
        }

        public boolean equals(Object o) {
            return equals((OperationFacts) o);
        }

        public void setLocation(IterationList loc) {
            this.location = loc;
        }

        public IterationList getLocation() {
            return location;
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