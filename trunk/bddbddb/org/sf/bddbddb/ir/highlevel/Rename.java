// Rename.java, created Jun 29, 2004 12:25:20 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir.highlevel;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import org.sf.bddbddb.Relation;

/**
 * Rename
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Rename extends HighLevelOperation {
    Relation r0, r1;

    Map/* <Pair,Attribute> */renames;

    /**
     * @param r0
     * @param r1
     */
    public Rename(Relation r0, Relation r1, Map/* <Pair,Attribute> */renames) {
        super();
        this.r0 = r0;
        this.r1 = r1;
        this.renames = renames;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return r0.toString() + " = " + getExpressionString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getExpressionString()
     */
    public String getExpressionString() {
        StringBuffer sb = new StringBuffer();
        sb.append("rename(");
        sb.append(r1.toString());
        for (Iterator i = renames.entrySet().iterator(); i.hasNext();) {
            Map.Entry p = (Map.Entry) i.next();
            sb.append(',');
            sb.append(p.getKey().toString());
            sb.append("->");
            sb.append(p.getValue().toString());
        }
        sb.append(")");
        return sb.toString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#visit(org.sf.bddbddb.ir.HighLevelOperationVisitor)
     */
    public Object visit(HighLevelOperationVisitor i) {
        return i.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getDest()
     */
    public Relation getRelationDest() {
        return r0;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.Operation#getSrcs()
     */
    public List getSrcs() {
        return Collections.singletonList(r1);
    }

    /**
     * @return Returns the source relation.
     */
    public Relation getSrc() {
        return r1;
    }

    /**
     * @return
     */
    public Map getRenameMap() {
        return renames;
    }
}