// ListFactory.java, created Tue Oct 19 22:39:10 1999 by pnkfelix
// Copyright (C) 1999 Felix S. Klock II <pnkfelix@mit.edu>
// Licensed under the terms of the GNU GPL; see COPYING for details.
package org.sf.bddbddb.util;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

/** <code>ListFactory</code> is a <code>List</code> generator.
    Subclasses should implement constructions of specific types of  
    <code>List</code>s.  <code>ListFactory</code> also has a set of
    static helper methods for building <code>List</code> objects.
 * 
 * @author  Felix S. Klock II <pnkfelix@mit.edu>
 * @version $Id$
 */
public abstract class ListFactory extends CollectionFactory {
    
    /** Returns a <code>ListFactory</code> that generates
    <code>ArrayList</code>s. */
    public static ListFactory arrayListFactory = new ListFactory() {
        public java.util.List makeList(java.util.Collection c) {
            return new java.util.ArrayList(c);
        }
        public List makeList(int i) {
            return new java.util.ArrayList(i);
        }
    
    };

    /** A <code>ListFactory</code> that generates <code>LinkedList</code>s. */
    public static final ListFactory linkedListFactory = new ListFactory() {
        public java.util.List makeList(java.util.Collection c) {
            return new java.util.LinkedList(c);
        }
    };
    
    /** Creates a <code>ListFactory</code>. */
    public ListFactory() { }
    
    /** Generates a new, mutable, empty <code>List</code>. */
    public final List makeList() {
        return makeList(Collections.EMPTY_LIST);
    }

    /** Generates a new, mutable, empty <code>List</code>, using 
        <code>initialCapacity</code> as a hint to use for the capacity
        for the produced <code>List</code>. */
    public List makeList(int initialCapacity) {
        return makeList();
    }

    /** Generates a new mutable <code>List</code>, using the elements
        of <code>c</code> as a template for its initial contents. 
    */
    public abstract List makeList(Collection c); 

    /* (non-Javadoc)
     * @see org.sf.bddbddb.util.CollectionFactory#makeCollection(int)
     */
    public final Collection makeCollection(int initCapacity) {
        return makeList(initCapacity);
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.util.CollectionFactory#makeCollection(java.util.Collection)
     */
    public final Collection makeCollection(Collection c) {
        return makeList(c);
    }

}
