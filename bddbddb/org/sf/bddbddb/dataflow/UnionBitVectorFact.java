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
        Assert._assert(location == ((BitVectorFact) that).location);
        BitString thatS = ((BitVectorFact) that).fact;
        BitString newS = new BitString(this.fact.size());
        newS.or(this.fact);
        boolean b = newS.or(thatS);
        if (!b) return this;
        UnionBitVectorFact f = create(newS);
        f.location = this.location;
        return f;
    }

    public Fact copy(IterationList list) {
        UnionBitVectorFact f = create(fact);
        f.location = list;
        return f;
    }
}