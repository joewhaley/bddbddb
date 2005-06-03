// Universe.java, created Mar 17, 2004 8:30:37 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

/**
 * A Universe is a special kind of variable that represents all values in
 * a domain.
 * 
 * @author John Whaley
 * @version $Id$
 */
public class Universe extends Variable {
    
    /**
     * Create a universe on the given domain.
     */
    public Universe(Domain fd) {
        super("*", fd);
    }

}
