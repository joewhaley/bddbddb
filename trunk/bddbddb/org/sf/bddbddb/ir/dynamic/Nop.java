/*
 * Created on Jul 8, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.ir.dynamic;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.Operation;

/**
 * @author Collective
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class Nop extends DynamicOperation {
    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.dynamic.DynamicOperation#visit(org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor)
     */
    public Object visit(DynamicOperationVisitor i) {
        return i.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return getExpressionString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getRelationDest()
     */
    public Relation getRelationDest() {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.EMPTY_LIST;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getExpressionString()
     */
    public String getExpressionString() {
        return "nop" + Integer.toString(id);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#setRelationDest(org.sf.bddbddb.Relation)
     */
    public void setRelationDest(Relation dest) {
    }

    public Operation copy() {
        return new Nop();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#replaceSrc(org.sf.bddbddb.Relation,
     *      org.sf.bddbddb.Relation)
     */
    public void replaceSrc(Relation r_old, Relation r_new) {
    }
}