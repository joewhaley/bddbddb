// PathNumbering.java, created Aug 16, 2003 1:49:33 AM by joewhaley
// Copyright (C) 2003 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.util;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.StringTokenizer;
import java.io.DataOutput;
import java.io.IOException;
import java.math.BigInteger;

/**
 * PathNumbering
 * 
 * @author John Whaley
 * @version $Id$
 */
public abstract class PathNumbering {
    public abstract BigInteger countPaths(Collection roots,
        Navigator navigator, Map initialMap);

    public abstract Range getRange(Object o);

    public abstract Range getEdge(Object from, Object to);

    public BigInteger countPaths(Graph graph) {
        return countPaths(graph.getRoots(), graph.getNavigator(), null);
    }

    public Range getEdge(Pair edge) {
        return getEdge(edge.left, edge.right);
    }

    public void dotGraph(DataOutput out, Collection roots, Navigator navigator)
        throws IOException {
        out.writeBytes("digraph \"PathNumbering\" {\n");
        out.writeBytes("  concentrate=true; node[fontsize=7];\n");
        LinkedList toVisit = new LinkedList();
        toVisit.addAll(roots);
        IndexMap m = new IndexMap("NodeMap");
        while (!toVisit.isEmpty()) {
            Object source = toVisit.removeFirst();
            int j = m.get(source);
            out.writeBytes("  n" + j + " [label=\"" + source + "\"];\n");
            for (Iterator i = navigator.next(source).iterator(); i.hasNext();) {
                Object target = i.next();
                if (!m.contains(target)) {
                    toVisit.add(target);
                }
                int k = m.get(target);
                Range r = getEdge(source, target);
                out.writeBytes("  n" + j + " -> n" + k + " [label=\"" + r
                    + "\"];\n");
            }
        }
        out.writeBytes("}\n");
    }
    public static class Range {
        public Number low, high;

        public Range(int l, int h) {
            this.low = new Integer(l);
            this.high = new Integer(h);
        }

        public Range(Number l, Number h) {
            this.low = l;
            this.high = h;
        }

        public Range(Number l, BigInteger h) {
            this.low = l;
            this.high = fromBigInt(h);
        }

        public Range(BigInteger l, Number h) {
            this.low = fromBigInt(l);
            this.high = h;
        }

        public Range(BigInteger l, BigInteger h) {
            this.low = fromBigInt(l);
            this.high = fromBigInt(h);
        }

        public String toString() {
            return "<" + low + ',' + high + '>';
        }

        public boolean equals(Range r) {
            return low.equals(r.low) && high.equals(r.high);
        }

        public boolean equals(Object o) {
            try {
                return equals((Range) o);
            } catch (ClassCastException x) {
                return false;
            }
        }

        public int hashCode() {
            return low.hashCode() ^ high.hashCode();
        }

        public static Range read(StringTokenizer st) {
            long lo = Long.parseLong(st.nextToken());
            long hi = Long.parseLong(st.nextToken());
            return new Range(new Long(lo), new Long(hi));
        }
    }

    /** Converts the given Number to BigInteger representation. */
    public static BigInteger toBigInt(Number n) {
        if (n instanceof BigInteger) return (BigInteger) n;
        else return BigInteger.valueOf(n.longValue());
    }

    /**
     * Converts the given BigInteger to a potentially smaller Number
     * representation.
     */
    public static Number fromBigInt(BigInteger n) {
        int bits = n.bitLength();
        if (bits < 32) return new Integer(n.intValue());
        if (bits < 64) return new Long(n.longValue());
        return n;
    }
}