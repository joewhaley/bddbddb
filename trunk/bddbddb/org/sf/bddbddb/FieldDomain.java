// FieldDomain.java, created Mar 16, 2004 3:44:18 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.io.DataInput;
import java.io.IOException;

import org.sf.bddbddb.util.IndexMap;
import org.sf.bddbddb.util.IndexedMap;

/**
 * FieldDomain
 * 
 * @author jwhaley
 * @version $Id$
 */
public class FieldDomain {
    
    String name;
    long size;
    IndexedMap map;
    
    /**
     * @param name
     * @param size
     */
    public FieldDomain(String name, long size) {
        super();
        this.name = name;
        this.size = size;
    }
    
    public void loadMap(DataInput in) throws IOException {
        //map = IndexMap.load(name, in);
        map = IndexMap.loadStringMap(name, in);
    }
    
    public String toString() {
        return name;
    }
    
    public String toString(int val) {
        if (map == null) return Integer.toString(val);
        else return map.get(val).toString();
    }
    
    public int namedConstant(String constant) {
        if (map == null) throw new IllegalArgumentException("No constant map for FieldDomain "+name+" in which to look up constant "+constant);
        if (!map.contains(constant)) throw new IllegalArgumentException("Constant "+constant+" not found in map for relation "+name);
        return map.get(constant);
    }
}
