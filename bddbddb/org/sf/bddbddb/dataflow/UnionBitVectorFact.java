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
 * @version $Id$
 */
public class UnionBitVectorFact extends BitVectorFact {
    public UnionBitVectorFact(int setSize) {
        super(setSize);
    }

    public UnionBitVectorFact(BitString s) {
        super(s);
    }

    public UnionBitVectorFact create(BitString s) {
        return new UnionBitVectorFact(s);
    }

    public Fact join(Fact that) {
        BitString thatS = ((BitVectorFact) that).fact;
        BitString newS = new BitString(this.fact.size());
        newS.or(this.fact);
        boolean b = newS.or(thatS);
        if (!b) return this;
        return create(newS);
    }

    public void setLocation(IterationList list) {
    }

    public IterationList getLocation() {
        Assert.UNREACHABLE("");
        return null;
    }

    public Fact copy(IterationList list) {
        return create(fact);
    }
}