// NodeWrapperIndexMap.java
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import org.sf.bddbddb.StringWrapper;

/**
 * An IndexMap for Wrappers. Always prefer other wrappers 
 * to stringwrappers. 
 * 
 * @author jzhuang
 */
public class NodeWrapperIndexMap implements IndexedMap {
    private final String name;
    private final HashMap hash;
    private final ArrayList list;
    private final boolean trace;

    public NodeWrapperIndexMap(String name) {
        this.name = name;
        hash = new HashMap();
        list = new ArrayList();
        trace = false;
    }

    public NodeWrapperIndexMap(String name, int size) {
        this.name = name;
        hash = new HashMap(size);
        list = new ArrayList(size);
        trace = false;
    }

    public NodeWrapperIndexMap(String name, int size, boolean t) {
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
        else if (!(o instanceof StringWrapper)) {
            Object w = list.get(i.intValue());
            if (w instanceof StringWrapper) {
                // evict old entry
                list.set(i.intValue(), o);
                hash.remove(o);
                hash.put(o, i);
            }
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
        for (Iterator j =iterator(); j.hasNext(); ) {
            Object o = j.next();
            out.write(o + "\n");
        }
    }

    public static NodeWrapperIndexMap loadStringWrapperMap(String name, BufferedReader in)
        throws IOException {
        NodeWrapperIndexMap dis = new NodeWrapperIndexMap(name);
        for (;;) {
            String s = in.readLine();
            if (s == null) break;
            StringWrapper o = new StringWrapper(s);
            dis.hash.put(o, new Integer(dis.list.size()));
            dis.list.add(o);
        }
        return dis;
    }
}
