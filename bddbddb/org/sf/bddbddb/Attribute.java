// Attribute.java, created Jun 29, 2004 12:37:11 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

/**
 * Attribute
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Attribute {
    
    String attributeName;
    Domain attributeDomain;
    String attributeOptions;
    
    /**
     * @param name
     * @param domain
     * @param options
     */
    public Attribute(String name, Domain domain, String options) {
        this.attributeName = name;
        this.attributeDomain = domain;
        this.attributeOptions = options;
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return attributeName;
    }
    
}
