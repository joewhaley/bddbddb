// Problem.java, created Jul 3, 2004 1:17:45 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.dataflow;

import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.ir.Operation;

/**
 * Problem
 * 
 * @author John Whaley
 * @version $Id$
 */
public abstract class Problem {
    
    public abstract TransferFunction getTransferFunction(Operation o);
    
    public abstract Fact getBoundary();
    
    public boolean compare(Fact f1, Fact f2) {
        return f1.equals(f2);
    }
    
    public abstract static class Fact {
        public abstract Fact join(Fact that);
        public abstract Fact copy(IterationList loc);
        public abstract void setLocation(IterationList loc);
        public abstract IterationList getLocation();
    }
    
    public abstract static class TransferFunction {
        public abstract Fact apply(Fact f);
    }
    
}
