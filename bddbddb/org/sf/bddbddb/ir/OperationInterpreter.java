// OperationInterpreter.java, created Jul 3, 2004 11:50:51 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import org.sf.bddbddb.ir.dynamic.DynamicInterpreter;
import org.sf.bddbddb.ir.highlevel.HighLevelInterpreter;
import org.sf.bddbddb.ir.lowlevel.LowLevelInterpreter;

/**
 * OperationInterpreter
 * 
 * @author John Whaley
 * @version $Id$
 */
public interface OperationInterpreter extends OperationVisitor, HighLevelInterpreter, LowLevelInterpreter, DynamicInterpreter {
}
