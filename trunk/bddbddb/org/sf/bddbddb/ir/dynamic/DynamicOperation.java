package org.sf.bddbddb.ir.dynamic;

import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.ir.OperationVisitor;

/**
 * @author Collective
 */
public abstract class DynamicOperation extends Operation {
    /**
     * @param i
     * @return
     */
    public Object visit(OperationVisitor i) {
        return visit((DynamicOperationVisitor) i);
    }

    /**
     * @param i
     * @return
     */
    public abstract Object visit(DynamicOperationVisitor i);
}