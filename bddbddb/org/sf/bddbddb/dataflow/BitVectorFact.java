/*
 * Created on Jul 6, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.dataflow;

import org.sf.bddbddb.util.BitString;
import org.sf.bddbddb.util.BitString.BitStringIterator;

/**
 * @author Collective
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public abstract class BitVectorFact implements Problem.Fact {
    protected final BitString fact;

    protected BitVectorFact(int setSize) {
        fact = new BitString(setSize);
    }

    protected BitVectorFact(BitString s) {
        this.fact = s;
    }

    public boolean equals(Object o) {
        if (o instanceof BitVectorFact) {
            return this.fact.equals(((BitVectorFact) o).fact);
        }
        return false;
    }
    
    public String toString() {
        return fact.toString();
    }
}