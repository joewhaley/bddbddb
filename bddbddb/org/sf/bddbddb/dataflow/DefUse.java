//DefUse.java, created Jul 3, 2004 9:53:25 PM by jwhaley
//Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
//Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.dataflow;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.MultiMap;

/**
 * DefUse
 * 
 * @author jwhaley
 * @version $Id$
 */
public class DefUse extends RelationProblem {
    
    MultiMap/*<Relation,Operation>*/ defs;
    MultiMap/*<Relation,Operation>*/ uses;
    
    public DefUse() {
        this.defs = new GenericMultiMap();
        this.uses = new GenericMultiMap();
    }
    
    public Collection/*<Operation>*/ getDefs(Relation r) {
        return defs.getValues(r);
    }
    
    public Collection/*<Operation>*/ getUses(Relation r) {
        return uses.getValues(r);
    }
    
    public class DefUseFact extends RelationFact {
        
        Set defs;
        IterationList location;
        
        DefUseFact(Set defs) {
            this.defs = defs;
        }
        
        public Set getDefs() {
            return defs;
        }
        
        public Fact copy(IterationList list) {
            Set defs = new HashSet(this.defs);
            return new DefUseFact(defs);
        }
        
        public Fact join(Fact that) {
            Set newDefs = new HashSet(this.defs);
            //if (that != null)
                newDefs.addAll(((DefUseFact) that).defs);
            Fact f = new DefUseFact(newDefs);
            return f;
        }
        
        public IterationList getLocation() {
            return location;
        }

        public void setLocation(IterationList block) {
            this.location = block;
        }
}
    
    public boolean direction() { return true; }
    
    public TransferFunction getTransferFunction(Operation op) {
        return new DefUseTransferFunction(op);
    }
    
    public class DefUseTransferFunction extends TransferFunction {
        
        Operation op;
        
        DefUseTransferFunction(Operation op) {
            this.op = op;
            if (op.getRelationDest() != null) {
                defs.add(op.getRelationDest(), op);
            }
            for (Iterator i = op.getSrcs().iterator(); i.hasNext(); ) {
                Object src = i.next();
                uses.add(src, op);
            }
        }
        
        public Fact apply(Fact f) {
            if (op.getRelationDest() == null) return f;
            DefUseFact duf = new DefUseFact(Collections.singleton(op));
            RelationFacts rf = (RelationFacts) f;
            rf.relationFacts.put(op.getRelationDest(), duf);
            return rf;
        }
        
    }
}
