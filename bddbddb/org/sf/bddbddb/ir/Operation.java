// Operation.java, created Jun 29, 2004 12:24:59 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

/**
 * Operation
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Operation {
    
    /**
     * @param i
     * @return
     */
    public abstract Object perform(Interpreter i);
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public abstract String toString();
    
}
