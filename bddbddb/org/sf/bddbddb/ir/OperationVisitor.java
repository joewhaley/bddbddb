// OperationVisitor.java, created Jul 3, 2004 11:50:51 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor;
import org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor;
import org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor;

/**
 * OperationVisitor
 * 
 * @author John Whaley
 * @version $Id$
 */
public interface OperationVisitor extends HighLevelOperationVisitor, LowLevelOperationVisitor, DynamicOperationVisitor {
}