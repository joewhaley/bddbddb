// DataflowSolver.java, created Jul 4, 2004 2:30:15 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.dataflow;

import java.util.HashMap;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Map;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.dataflow.Problem.Fact;
import org.sf.bddbddb.dataflow.Problem.TransferFunction;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.util.Assert;

/**
 * DataflowSolver
 * 
 * @author John Whaley
 * @version $Id$
 */
public class DataflowSolver {
    
    boolean TRACE = false;
    
    /** Matches blocks to their dataflow information. */
    Map/*<IterationList,Fact>*/ blockToFact;
    
    public DataflowSolver() {
        blockToFact = new HashMap();
    }
    
    /** Resets dataflow information. */
    public void reset() {
        blockToFact.clear();
    }
    
    /** Returns the dataflow information for a given block. */
    public Fact getFact(IterationList block) {
        return (Fact) blockToFact.get(block);
    }
    
    public DataflowIterator getIterator(Problem p, IterationList g) {
        return new DataflowIterator(p, g);
    }
    
    public class DataflowIterator implements ListIterator {

        Problem p;
        Fact fact;
        IterationList block;
        ListIterator ops;
        DataflowIterator nested;
        
        public DataflowIterator(Problem p, IterationList block) {
            this(p, DataflowSolver.this.getFact(block), block);
        }
        
        public DataflowIterator(Problem p, Fact startingFact, IterationList block) {
            this.p = p;
            this.fact = startingFact;
            this.block = block;
            this.ops = block.iterator();
        }
        
        public Fact getFact() {
            if (nested != null) return nested.getFact();
            return fact;
        }
        
        /* (non-Javadoc)
         * @see java.util.Iterator#hasNext()
         */
        public boolean hasNext() {
            if (nested != null && nested.hasNext()) return true;
            return ops.hasNext();
        }

        public boolean hasPrevious() {
            throw new UnsupportedOperationException();
        }
        
        public Object next() {
            if (nested != null) {
                if (!nested.hasNext()) {
                    if (TRACE) System.out.println("Exiting "+nested.block);
                    nested = null;
                } else {
                    return nested.next();
                }
            }
            Object o = ops.next();
            if (o instanceof Operation) {
                Operation op = (Operation) o;
                TransferFunction tf = p.getTransferFunction(op);
                fact = tf.apply(fact);
            } else {
                IterationList list = (IterationList) o;
                fact = (Fact) blockToFact.get(list);
            }
            return o;
        }
        
        public Object previous() {
            throw new UnsupportedOperationException();
        }
        
        public int nextIndex() {
            throw new UnsupportedOperationException();
        }
        
        public int previousIndex() {
            throw new UnsupportedOperationException();
        }
        
        public void enter(IterationList list) {
            if (nested != null) nested.enter(list);
            else {
                if (TRACE) System.out.println("Entering "+list);
                nested = new DataflowIterator(p, list);
            }
        }
        
        /* (non-Javadoc)
         * @see java.util.Iterator#remove()
         */
        public void remove() {
            if (nested != null) nested.remove();
            else ops.remove();
        }
        
        public void set(Object o) {
            if (nested != null) nested.set(o);
            else ops.set(o);
        }
        
        public void add(Object o) {
            if (nested != null) nested.add(o);
            else ops.add(o);
        }
    }
    
    public void solve(Problem p, IterationList g) {
        Fact startFact = p.getBoundary();
        startFact.setLocation(g);
        solve(startFact, p, g);
    }
    
    Fact solve(Fact currentFact, Problem p, IterationList g) {
        // Cache current dataflow information at start of block.
        Fact startFact = currentFact.copy(g);
        for (;;) {
            Assert._assert(startFact.getLocation() == g);
            Assert._assert(currentFact.getLocation() == g);
            blockToFact.put(g, startFact);
            for (Iterator i = g.iterator(); i.hasNext(); ) {
                Object o = i.next();
                if (o instanceof IterationList) {
                    IterationList list = (IterationList) o;
                    if (TRACE) System.out.println("Entering "+list);
                    currentFact.setLocation(list);
                    currentFact = solve(currentFact, p, list);
                    currentFact.setLocation(g);
                    if (TRACE) System.out.println("Leaving "+list);
                } else {
                    Operation op = (Operation) o;
                    if (TRACE) System.out.println("   Operation: "+op);
                    TransferFunction tf = p.getTransferFunction(op);
                    currentFact = tf.apply(currentFact);
                }
                Assert._assert(startFact.getLocation() == g);
                Assert._assert(currentFact.getLocation() == g);
            }
            if (!g.isLoop()) break;
            Fact joinResult = startFact.join(currentFact);
            if (joinResult.equals(startFact)) {
                if (TRACE) System.out.println("No change after join, exiting.");
                currentFact = joinResult;
                break;
            }
            if (TRACE) System.out.println("Result: "+joinResult);
            if (TRACE) System.out.println(g+" changed, iterating again...");
            startFact = joinResult;
            currentFact = startFact.copy(g);
        }
        return currentFact;
    }
    
}
