// Interpreter.java, created Jun 29, 2004 12:50:19 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

/**
 * Interpreter
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Interpreter {

    /**
     * @param op
     * @return
     */
    public abstract Object perform(Join op);
    
    /**
     * @param op
     * @return
     */
    public abstract Object perform(Project op);
    
    /**
     * @param op
     * @return
     */
    public abstract Object perform(Rename op);

    /**
     * @param op
     * @return
     */
    public abstract Object perform(Union op);

    /**
     * @param op
     * @return
     */
    public abstract Object perform(Difference op);

    /**
     * @param op
     * @return
     */
    public abstract Object perform(JoinConstant op);
    
    /**
     * @param op
     * @return
     */
    public abstract Object perform(GenConstant op);
}
