// Copy.java, created Jul 2, 2004 12:28:31 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.highlevel;

import java.util.Collections;
import java.util.List;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.Operation;

/**
 * Copy
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Copy extends HighLevelOperation {
    Relation r0, r1;

    /**
     * @param r0
     * @param r1
     */
    public Copy(Relation r0, Relation r1) {
        super();
        this.r0 = r0;
        this.r1 = r1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.HighLevelOperationVisitor)
     */
    public Object visit(HighLevelOperationVisitor i) {
        return i.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString() + " = " + getExpressionString();
    }

    /**
     * @return
     */
    public String getExpressionString() {
        return "copy(" + r1.toString() + ")";
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getRelationDest() {
        return r0;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.singletonList(r1);
    }

    /**
     * @return Returns the source relation.
     */
    public Relation getSrc() {
        return r1;
    }

    public Operation copy() {
        return new Copy(r0, r1);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#replaceSrc(org.sf.bddbddb.Relation,
     *      org.sf.bddbddb.Relation)
     */
    public void replaceSrc(Relation r_old, Relation r_new) {
        if (r1 == r_old) r1 = r_new;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#setRelationDest(org.sf.bddbddb.Relation)
     */
    public void setRelationDest(Relation r0) {
        this.r0 = r0;
    }
}