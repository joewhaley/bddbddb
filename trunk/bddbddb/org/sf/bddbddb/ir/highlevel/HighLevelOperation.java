package org.sf.bddbddb.ir.highlevel;

import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.ir.OperationVisitor;

/**
 * @author Collective
 */
public abstract class HighLevelOperation extends Operation {
    /**
     * @param i
     * @return
     */
    public Object visit(OperationVisitor i) {
        return visit((HighLevelOperationVisitor) i);
    }

    /**
     * @param i
     * @return
     */
    public abstract Object visit(HighLevelOperationVisitor i);
}