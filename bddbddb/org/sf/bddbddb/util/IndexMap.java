// IndexMap.java, created Jun 15, 2003 2:04:05 AM by joewhaley
// Copyright (C) 2003 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;

/**
 * An IndexMap provides a fast mapping between elements and (integer) indices.
 * 
 * @author John Whaley
 * @version $Id$
 */
public class IndexMap implements IndexedMap {
    private final String name;
    private final HashMap hash;
    private final ArrayList list;
    private final boolean trace;

    public IndexMap(String name) {
        this.name = name;
        hash = new HashMap();
        list = new ArrayList();
        trace = false;
    }

    public IndexMap(String name, int size) {
        this.name = name;
        hash = new HashMap(size);
        list = new ArrayList(size);
        trace = false;
    }

    public IndexMap(String name, int size, boolean t) {
        this.name = name;
        hash = new HashMap(size);
        list = new ArrayList(size);
        trace = t;
    }

    public int get(Object o) {
        Integer i = (Integer) hash.get(o);
        if (i == null) {
            hash.put(o, i = new Integer(list.size()));
            list.add(o);
            if (trace) System.out.println(this + "[" + i + "] = " + o);
        }
        return i.intValue();
    }

    public Object get(int i) {
        return list.get(i);
    }

    public boolean contains(Object o) {
        return hash.containsKey(o);
    }

    public int size() {
        return list.size();
    }

    public String toString() {
        return name;
    }

    public Iterator iterator() {
        return list.iterator();
    }

    public void clear() {
        hash.clear();
        list.clear();
    }

    public boolean addAll(Collection c) {
        int before = size();
        for (Iterator i = c.iterator(); i.hasNext();) {
            get(i.next());
        }
        return before != size();
    }

    public void dumpStrings(final BufferedWriter out) throws IOException {
        for (int j = 0; j < size(); ++j) {
            Object o = get(j);
            String s;
            if (o != null) {
                s = o.toString();
                Assert._assert(s.indexOf('\n') == -1);
                Assert._assert(s.indexOf('\r') == -1);
            } else {
                s = "null";
            }
            out.write(s + "\n");
        }
    }

    public static IndexMap loadStringMap(String name, BufferedReader in)
        throws IOException {
        IndexMap dis = new IndexMap(name);
        for (;;) {
            String o = in.readLine();
            if (o == null) break;
            dis.hash.put(o, new Integer(dis.list.size()));
            dis.list.add(o);
        }
        return dis;
    }
}
