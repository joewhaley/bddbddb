// Operation.java, created Jun 29, 2004 12:24:59 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.List;
import org.sf.bddbddb.Relation;

/**
 * Operation
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Operation {
    static int opNumber = 0;
    public int id;

    public Operation() {
        id = ++opNumber;
    }

    /**
     * @param i
     * @return
     */
    public abstract Object visit(OperationVisitor i);

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public abstract String toString();

    /**
     * @return
     */
    public abstract Relation getDest();

    /**
     * @return
     */
    public abstract List/* <Relation> */getSrcs();
}