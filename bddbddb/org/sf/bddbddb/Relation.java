// Relation.java, created Mar 16, 2004 12:39:48 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Iterator;
import java.util.List;
import java.io.IOException;

/**
 * Relation
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class Relation {
    String name;
    List/* <Attribute> */attributes;
    Relation negated;
    public int id;

    /**
     * Create a new Relation.
     * 
     * @param name
     * @param attributes
     */
    public Relation(Solver solver, String name, List attributes) {
        super();
        this.name = name;
        this.attributes = attributes;
        this.id = solver.registerRelation(this);
        for (Iterator i = attributes.iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            if (a.relation == null) a.relation = this;
        }
    }

    public abstract void initialize();

    public abstract void load() throws IOException;

    public abstract void loadTuples() throws IOException;

    public abstract void save() throws IOException;

    public abstract void saveNegated() throws IOException;

    public abstract void saveTuples() throws IOException;

    public abstract void saveNegatedTuples() throws IOException;

    public abstract Relation copy();

    public abstract void free();

    /**
     * @return number of tuples in relation
     */
    public int size() {
        return (int) dsize();
    }

    /**
     * @return number of tuples in relation
     */
    public abstract double dsize();

    /**
     * Return an iterator over the tuples of this relation.
     * 
     * @return iterator of long[]
     */
    public abstract TupleIterator iterator();

    /**
     * Return an iterator over the values in the kth field of the relation. k is
     * zero-based.
     * 
     * @param k
     *            zero-based field number
     * @return iterator of long[]
     */
    public abstract TupleIterator iterator(int k);

    /**
     * Return an iterator over the tuples where the kth field has value j. k is
     * zero-based.
     * 
     * @param k
     *            zero-based field number
     * @param j
     *            value
     * @return iterator of long[]
     */
    public abstract TupleIterator iterator(int k, long j);

    /**
     * Return an iterator over the tuples where the fields match the values in
     * the given array. A -1 value in the array matches any value.
     * 
     * @param j
     *            values
     * @return iterator of long[]
     */
    public abstract TupleIterator iterator(long[] j);

    /**
     * Returns true iff this relation contains a tuple where the kth field is
     * value j. k is zero-based.
     * 
     * @param k
     *            zero-based field number
     * @param j
     *            value
     * @return whether the given value appears in the given field
     */
    public abstract boolean contains(int k, long j);

    /**
     * Return the negated form of this relation, or null if it does not exist.
     * 
     * @return negated version of this relation, or null
     */
    public Relation getNegated() {
        return negated;
    }

    /**
     * Get or create the negated form of this relation.
     * 
     * @param solver
     *            solver
     * @return negated version of this relation
     */
    public Relation makeNegated(Solver solver) {
        if (negated != null) return negated;
        negated = solver.createRelation("!" + name, attributes);
        negated.negated = this;
        return negated;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return name;
    }

    /**
     * @return Returns the attributes.
     */
    public List getAttributes() {
        return attributes;
    }

    /**
     * @param x
     * @return
     */
    public Attribute getAttribute(int x) {
        return (Attribute) attributes.get(x);
    }

    /**
     * @param x
     * @return
     */
    public Attribute getAttribute(String x) {
        for (Iterator i = attributes.iterator(); i.hasNext(); ) {
            Attribute a = (Attribute) i.next();
            if (x.equals(a.attributeName)) return a;
        }
        return null;
    }
    
    /**
     * @return
     */
    public int numberOfAttributes() {
        return attributes.size();
    }
}