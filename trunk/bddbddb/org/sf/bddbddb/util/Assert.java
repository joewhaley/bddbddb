// Assert.java, created Jun 15, 2004 1:39:55 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.util;

/**
 * Assert
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Assert {
    
    /**
     * Assert that the given predicate is true.  If it is false, we
     * print a stack trace and exit.
     * 
     * @param b predicate to check
     */
    public static void _assert(boolean b) {
        _assert(b, "");
    }

    /**
     * Assert that the given predicate is true.  If it is false, we print
     * the given reason and a stack trace, and exit.
     * 
     * @param b predicate to check
     * @param reason string to print if the assertion fails
     */
    public static void _assert(boolean b, String reason) {
        if (!b) {
            System.err.println("Assertion Failure!");
            System.err.println(reason);
            throw new InternalError();
        }
    }

    /**
     * Print an UNREACHABLE message and a stack trace and exit.
     * 
     * @param s message to print
     */
    public static void UNREACHABLE(String s) {
        _assert(false, "UNREACHABLE: " + s);
    }

}
