package org.sf.bddbddb.ir;

import org.sf.bddbddb.ir.highlevel.HighLevelInterpreter;
import org.sf.bddbddb.ir.lowlevel.LowLevelInterpreter;

/**
 * @author Collective
 */
public interface Interpreter extends OperationVisitor, HighLevelInterpreter, LowLevelInterpreter {
}
