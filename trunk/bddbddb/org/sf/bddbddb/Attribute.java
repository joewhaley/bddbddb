// Attribute.java, created Jun 29, 2004 12:37:11 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

/**
 * An Attribute represents a single attribute of a relation.
 * Every Attribute has a name, a domain, and an optional option string.
 * 
 * Attribute objects are globally unique --- there is exactly one Attribute
 * object for every distinct attribute in the program.
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Attribute {
    protected String attributeName;
    protected Domain attributeDomain;
    protected String attributeOptions;
    protected Relation relation;

    /**
     * Constructs a new Attribute object.
     * This should only be called internally.
     * 
     * @param name  name of attribute
     * @param domain  domain of attribute
     * @param options  options for attribute
     */
    Attribute(String name, Domain domain, String options) {
        this.attributeName = name;
        this.attributeDomain = domain;
        this.attributeOptions = options;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return attributeName;
    }

    /**
     * Returns the domain of this attribute.
     * 
     * @return domain
     */
    public Domain getDomain() {
        return attributeDomain;
    }

    /**
     * Returns the options for this attribute.
     * 
     * @return options
     */
    public String getOptions() {
        return attributeOptions;
    }

    /**
     * Sets the relation that this attribute is associated with.
     * This should only be called internally.
     * 
     * @param r
     */
    void setRelation(Relation r) {
        this.relation = r;
    }
    
    /**
     * Returns the relation that this attribute is associated with.
     * 
     * @return options
     */
    public Relation getRelation() {
        return relation;
    }
}
