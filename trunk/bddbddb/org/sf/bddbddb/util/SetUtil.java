// SetUtil.java, created Aug 21, 2004 1:31:06 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.util;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

/**
 * SetUtil
 * 
 * @author John Whaley
 * @version $Id$
 */
public abstract class SetUtil {
    
    public static Collection powerSet(Collection c) {
        return powerSet(ListFactory.arrayListFactory, c);
    }
    
    /**
     * The powerSet method returns a Collection
     * whose elements are exactly the subsets of c, with no repetitions.
     * More precisely, if c is a Collection, possibly with 
     * repetitions, the result powerSet(c) is a Collection u
     * without repetitions whose elements represent all the subsets of
     * v.
     */
    public static Collection powerSet(CollectionFactory f, Collection c) {
        Iterator citer = c.iterator();
        Collection result = f.makeCollection();
        if (!citer.hasNext()) {
            // c is empty, so return its power
            // set, i.e., the set with the empty set
            // as its only element:
            result.add(f.makeCollection());
            return result;
        }
        // Pick an element x of c and let p be the power set of c - {x}.
        // Then p is the set of subsets of c not containing x.
        Object x = citer.next();
        Collection cminusx = f.makeCollection();
        while (citer.hasNext()) {
            cminusx.add(citer.next());
        }
        Collection p = powerSet(f, cminusx);
        // Build the power set of c by adding, for each s in p, s u {x}
        Iterator piter = p.iterator();
        while (piter.hasNext()) {
            Collection s = (Collection) piter.next();
            // make a copy of s and add x to it
            Collection t = uniquify(f, s);
            t.add(x);
            // add both s and t to the answer
            result.add(s);
            result.add(t);
        }
        return result;
    }
    
    /**
     * Given an input Collection that may contain duplicates
     * returns a Collection with the same elements but no
     * duplicates.
     */
    public static Collection uniquify(CollectionFactory f, Collection c) {
        if (c instanceof Set)              // fast path if we are using sets
            return (Set) f.makeCollection(c);
        
        Collection w = f.makeCollection(); // make an empty Collection
        Iterator i = c.iterator();         // we iterate over elements of c
        while (i.hasNext()) {
            Object y = i.next();
            if (!w.contains(y))            // if y is not in w add it
                w.add(y);
        }
        return w;                          // final answer is w
    }
}
