/*
 * Created on Jul 6, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.dataflow;

import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.dataflow.Problem.Fact;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.BitString;

/**
 * @author Collective
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class UnionBitVectorFact extends BitVectorFact {
    public UnionBitVectorFact(int setSize) {
        super(setSize);
    }

    public UnionBitVectorFact(BitString s) {
        super(s);
    }

    public Fact join(Fact that) {
        BitString thatS = ((BitVectorFact) that).fact;
        BitString newS = new BitString(this.fact.size());
        newS.or(this.fact);
        boolean b = newS.or(thatS);
        if (!b) return this;
        return new UnionBitVectorFact(newS);
    }

    public void setLocation(IterationList list) {
        Assert.UNREACHABLE("");
    }

    public IterationList getLocation() {
        Assert.UNREACHABLE("");
        return null;
    }

    public Fact copy(IterationList list) {
        Assert.UNREACHABLE("");
        return null;
    }
}