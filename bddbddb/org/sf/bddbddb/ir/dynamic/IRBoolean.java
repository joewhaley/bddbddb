/*
 * Created on Jul 7, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.ir.dynamic;

/**
 * @author Collective
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class IRBoolean {
    boolean bool;
    String name;

    public IRBoolean(String name, boolean bool) {
        this.name = name;
        this.bool = bool;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return name + "(" + Boolean.toString(bool) + ")";
    }

    /**
     * @return
     */
    public boolean value() {
        return bool;
    }

    /**
     * @param bool
     */
    public void set(boolean bool) {
        this.bool = bool;
    }

    /**
     * @return
     */
    public String getName() {
        return name;
    }
}