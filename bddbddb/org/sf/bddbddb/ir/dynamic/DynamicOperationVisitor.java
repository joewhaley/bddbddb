// LowLevelOperationVisitor.java, created Jul 3, 2004 11:50:51 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.dynamic;

/**
 * LowLevelOperationVisitor
 * 
 * @author John Whaley
 * @version $Id: LowLevelOperationVisitor.java,v 1.2 2004/07/07 06:30:23
 *          joewhaley Exp $
 */
public interface DynamicOperationVisitor {
    /**
     * @param op
     * @return
     */
    public abstract Object visit(If op);
}