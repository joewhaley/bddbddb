/*
 * Created on Jul 6, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.dataflow;

import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.util.BitString;

/**
 * BitVectorFact
 * 
 * @author Collective
 * @version $Id$
 */
public abstract class BitVectorFact implements Problem.Fact {
    protected final BitString fact;

    IterationList location;
    
    public void setLocation(IterationList list) {
        location = list;
    }

    public IterationList getLocation() {
        return location;
    }

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