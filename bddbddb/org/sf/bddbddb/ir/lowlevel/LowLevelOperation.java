// LowLevelOperation.java, created Jul 3, 2004 11:50:51 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.lowlevel;

import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.ir.OperationVisitor;

/**
 * LowLevelOperation
 * 
 * @author John Whaley
 * @version $Id$
 */
public abstract class LowLevelOperation extends Operation {
    /**
     * @param i  visitor
     * @return  the result from the visitor
     */
    public Object visit(OperationVisitor i) {
        return visit((LowLevelOperationVisitor) i);
    }

    /**
     * @param i  visitor
     * @return  the result from the visitor
     */
    public abstract Object visit(LowLevelOperationVisitor i);
}