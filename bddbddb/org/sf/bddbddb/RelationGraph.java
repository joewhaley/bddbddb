// RelationGraph.java, created May 4, 2004 4:08:32 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.io.PrintStream;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.Graph;
import org.sf.bddbddb.util.Navigator;
import org.sf.bddbddb.util.Pair;

/**
 * RelationGraph
 * 
 * @author jwhaley
 * @version $Id$
 */
public class RelationGraph implements Graph {
    boolean TRACE = true;
    PrintStream out = System.out;
    RuleTerm root;
    Variable rootVariable;
    List/* <RuleTerm> */edges;

    RelationGraph(RuleTerm root, Variable rootVar, List/* <RuleTerm> */edges) {
        this.root = root;
        this.rootVariable = rootVar;
        this.edges = edges;
    }

    RelationGraph(Relation roots, Relation edges) {
        Assert._assert(roots.attributes.size() == 1);
        Assert._assert(edges.attributes.size() == 2);
        Attribute a = (Attribute) roots.attributes.get(0);
        Domain fd = a.attributeDomain;
        this.rootVariable = new Variable(fd.toString(), fd);
        List varList = Collections.singletonList(rootVariable);
        this.root = new RuleTerm(varList, roots);
        Assert._assert(edges.getAttribute(0).attributeDomain == fd);
        Assert._assert(edges.getAttribute(1).attributeDomain == fd);
        List varList2 = new Pair(rootVariable, rootVariable);
        RuleTerm edge = new RuleTerm(varList2, edges);
        this.edges = Collections.singletonList(edge);
    }
    static class GraphNode {
        Variable v;
        long number;

        GraphNode(Variable var, long num) {
            this.v = var;
            this.number = num;
        }

        public int hashCode() {
            return v.hashCode() ^ (int) number;
        }

        public boolean equals(GraphNode that) {
            return this.v == that.v && this.number == that.number;
        }

        public boolean equals(Object o) {
            return equals((GraphNode) o);
        }

        public String toString() {
            return v.toString() + ":" + number;
        }
    }

    public static GraphNode makeGraphNode(Variable v, long num) {
        return new GraphNode(v, num);
    }
    Nav navigator = new Nav();
    class Nav implements Navigator {
        Collection getEdges(Object node, int fromIndex, int toIndex) {
            GraphNode gn = (GraphNode) node;
            if (TRACE) out.println("Getting edges of " + gn + " indices (" + fromIndex + "," + toIndex + ")");
            Collection c = new LinkedList();
            for (Iterator a = edges.iterator(); a.hasNext();) {
                RuleTerm rt = (RuleTerm) a.next();
                if (rt.variables.get(fromIndex) == gn.v) {
                    if (TRACE) out.println("Rule term " + rt + " matches");
                    Variable v2 = (Variable) rt.variables.get(toIndex);
                    TupleIterator i = rt.relation.iterator(fromIndex, gn.number);
                    while (i.hasNext()) {
                        long[] j = i.nextTuple();
                        c.add(new GraphNode(v2, j[toIndex]));
                    }
                }
            }
            if (TRACE) out.println("Edges: " + c);
            return c;
        }

        /*
         * (non-Javadoc)
         * 
         * @see joeq.Util.Graphs.Navigator#next(java.lang.Object)
         */
        public Collection next(Object node) {
            return getEdges(node, 0, 1);
        }

        /*
         * (non-Javadoc)
         * 
         * @see joeq.Util.Graphs.Navigator#prev(java.lang.Object)
         */
        public Collection prev(Object node) {
            return getEdges(node, 1, 0);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see joeq.Util.Graphs.Graph#getRoots()
     */
    public Collection getRoots() {
        Relation rootRelation = root.relation;
        int k = root.variables.indexOf(rootVariable);
        Collection roots = new LinkedList();
        TupleIterator i = rootRelation.iterator(k);
        while (i.hasNext()) {
            long j = i.nextTuple()[0];
            roots.add(new GraphNode(rootVariable, j));
        }
        if (TRACE) out.println("Roots of graph: " + roots);
        return roots;
    }

    /*
     * (non-Javadoc)
     * 
     * @see joeq.Util.Graphs.Graph#getNavigator()
     */
    public Navigator getNavigator() {
        return navigator;
    }
}