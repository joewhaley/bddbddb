// LowLevelOperationVisitor.java, created Jul 3, 2004 11:50:51 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.lowlevel;

/**
 * LowLevelOperationVisitor
 * 
 * @author John Whaley
 * @version $Id$
 */
public interface LowLevelOperationVisitor {
   /**
     * @param op
     * @return
     */
    public abstract Object visit(ApplyEx op);
    
    /**
     * @param op
     * @return
     */
    public abstract Object visit(Replace op);
}
