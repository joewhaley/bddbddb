// SetFactory.java, created Tue Oct 19 22:22:44 1999 by pnkfelix
// Copyright (C) 1999 Felix S. Klock II <pnkfelix@mit.edu>
// Licensed under the terms of the GNU GPL; see COPYING for details.
package org.sf.bddbddb.util;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

/** <code>SetFactory</code> is a <code>Set</code> generator.
    Subclasses should implement constructions of specific types of
    <code>Set</code>s.
 * 
 * @author  Felix S. Klock II <pnkfelix@mit.edu>
 * @version $Id$
 */
public abstract class SetFactory extends CollectionFactory {
    
    /** A <code>SetFactory</code> that generates <code>HashSet</code>s. */
    public static final SetFactory hashSetFactory = new SetFactory() {
            public java.util.Set makeSet(java.util.Collection c) {
                return new java.util.HashSet(c);
            }
            public Set makeSet(int i) {
                return new java.util.HashSet(i);
            }
    };
    
    /** Creates a <code>SetFactory</code>. */
    public SetFactory() {
        super();
    }
    
    /** Generates a new, mutable, empty <code>Set</code>. */
    public final java.util.Set makeSet() {
        return makeSet(Collections.EMPTY_SET);
    }

    /** Generates a new, mutable, empty <code>Set</code>, using
        <code>initialCapacity</code> as a hint to use for the capacity
        for the produced <code>Set</code>. */
    public java.util.Set makeSet(int initialCapacity) {
        return makeSet();
    }

    /** Generates a new mutable <code>Set</code>, using the elements
        of <code>c</code> as a template for its initial contents. 
    */ 
    public abstract Set makeSet(Collection c);
    
    /* (non-Javadoc)
     * @see org.sf.bddbddb.util.CollectionFactory#makeCollection(int)
     */
    public Collection makeCollection(int initialCapacity) {
        return makeSet(initialCapacity);
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.util.CollectionFactory#makeCollection(java.util.Collection)
     */
    public Collection makeCollection(Collection c) {
        return makeSet(c);
    }
}
