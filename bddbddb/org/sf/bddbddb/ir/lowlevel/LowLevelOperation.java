package org.sf.bddbddb.ir.lowlevel;

import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.ir.OperationVisitor;

/**
 * @author Collective
 */
public abstract class LowLevelOperation extends Operation {
    /**
     * @param i
     * @return
     */
    public Object visit(OperationVisitor i) {
        return visit((LowLevelOperationVisitor) i);
    }

    /**
     * @param i
     * @return
     */
    public abstract Object visit(LowLevelOperationVisitor i);
}