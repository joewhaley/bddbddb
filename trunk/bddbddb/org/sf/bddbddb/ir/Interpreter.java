// Interpreter.java, created Jun 29, 2004 12:50:19 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.io.IOException;

/**
 * Interpreter
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Interpreter implements OperationVisitor {
    /**
     * @param op
     * @return
     */
    public abstract Object visit(Join op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Project op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Rename op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Union op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Difference op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(JoinConstant op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(GenConstant op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Free op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Universe op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Zero op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Invert op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Copy op);

    /**
     * @param op
     * @return
     */
    public abstract Object visit(Save op);
}