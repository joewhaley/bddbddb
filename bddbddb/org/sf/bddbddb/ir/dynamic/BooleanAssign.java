/*
 * Created on Jul 7, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.ir.dynamic;

import org.sf.bddbddb.ir.Operation;

/**
 * @author Collective
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public abstract class BooleanAssign extends Operation {
    IRBoolean dest;

    public BooleanAssign(IRBoolean dest) {
        this.dest = dest;
    }

    public IRBoolean getBoolDest() {
        return dest;
    }
}