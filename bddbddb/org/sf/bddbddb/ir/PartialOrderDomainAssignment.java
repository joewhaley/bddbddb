// UFDomainAssignment.java, created Jul 11, 2004 12:59:33 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.io.DataOutput;
import java.io.IOException;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDSolver;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.Solver;
import org.sf.bddbddb.dataflow.PartialOrder.ConstraintGraph;
import org.sf.bddbddb.dataflow.PartialOrder.Constraints;
import org.sf.bddbddb.util.Pair;

/**
 * UFDomainAssignment
 * 
 * @author John Whaley
 * @version $Id$
 */
public class PartialOrderDomainAssignment extends UFDomainAssignment {
    List beforeConstraints;
    List ileavedConstraints;

    /**
     * @param s
     */
    public PartialOrderDomainAssignment(Solver s, Constraints[] constraintMap) {
        super(s, constraintMap);
        beforeConstraints = new LinkedList();
        ileavedConstraints = new LinkedList();
    }

    public void doAssignment() {
        super.doAssignment();
        setTotalOrder();
    }

    boolean wouldBeLegal(Object a1, Object a2) {
        if (!super.wouldBeLegal(a1, a2)) return false;
        List path = new LinkedList();
        ConstraintGraph graph = new ConstraintGraph(beforeConstraints);
        if (graph.isPath(a1, a2, path) || graph.isPath(a2, a1, path)) {
            if (TRACE) System.out.println("Cannot,rep cycle detected: " + path);
            return false;
        }
        return true;
    }

    boolean forceBefore(Object o1, Object o2) {
        beforeConstraints = updateConstraints(beforeConstraints);
        Object rep1 = uf.find(o1);
        Object rep2 = uf.find(o2);
        Pair tempConstraint = new Pair(rep1, rep2);
        if (beforeConstraints.contains(tempConstraint)) {
            if (TRACE) System.out.println(o1 + " already before " + o2);
            return true;
        }
        beforeConstraints.add(tempConstraint);
        List cycle = new LinkedList();
        if (!constraintsSatisfied(cycle)) {
            if (TRACE) System.out.println("rep cycle detected: " + cycle);
            beforeConstraints.remove(tempConstraint);
            return false;
        }
        if (TRACE) System.out.println("adding before constraint: " + tempConstraint);
        return true;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.DomainAssignment#forceBefore(org.sf.bddbddb.Relation, org.sf.bddbddb.Attribute, org.sf.bddbddb.Relation, org.sf.bddbddb.Attribute)
     */
    boolean forceBefore(Relation r1, Attribute a1, Relation r2, Attribute a2) {
        Pair p1 = new Pair(r1, a1);
        Pair p2 = new Pair(r2, a2);
        return forceBefore(p1, p2);
    }

    boolean forceInterleaved(Object o1, Object o2) {
        if (TRACE) System.out.println("Forcing " + o1 + " interleaved " + o2);
        //update constraint reps
        ileavedConstraints = updateConstraints(ileavedConstraints);
        Object rep1 = uf.find(o1);
        Object rep2 = uf.find(o2);
        Pair newConstraint = new Pair(rep1, rep2);
        if (ileavedConstraints.contains(newConstraint)) {
            if (TRACE) System.out.println(o1 + " already interleaved with " + o2);
            return true;
        }
        ileavedConstraints.add(newConstraint);
        if (TRACE) System.out.println("adding interleaved constraint: " + newConstraint);
        return true;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.DomainAssignment#forceBefore(org.sf.bddbddb.Relation, org.sf.bddbddb.Attribute, org.sf.bddbddb.Relation, org.sf.bddbddb.Attribute)
     */
    boolean forceInterleaved(Relation r1, Attribute a1, Relation r2, Attribute a2) {
        Pair p1 = new Pair(r1, a1);
        Pair p2 = new Pair(r2, a2);
        return forceInterleaved(p1, p2);
    }

    boolean constraintsSatisfied(List cycle) {
        if (TRACE) System.out.println("Before Constraints: " + beforeConstraints);
        ConstraintGraph graph = new ConstraintGraph(beforeConstraints);
        if (TRACE) System.out.println("Before graph: " + graph);
        return !graph.isCycle(cycle);
    }

    private List updateConstraints(List constraints) {
        List newCons = new LinkedList(constraints);
        List adds = new LinkedList();
        for (Iterator it = newCons.iterator(); it.hasNext();) {
            Pair c = (Pair) it.next();
            Object crep1 = uf.find(c.left);
            Object crep2 = uf.find(c.right);
            if (!crep1.equals(c.left) || !crep2.equals(c.right)) {
                it.remove();
                //Assert._assert(crep1 != crep2, c.toString());
                if (!crep1.equals(crep2)) adds.add(new Pair(crep1, crep2));
            }
        }
        newCons.addAll(adds);
        return newCons;
    }

    public String setTotalOrder() {
        if (beforeConstraints.size() == 0 && ileavedConstraints.size() == 0) {
            if (TRACE) System.out.println("No constraints specified using default ordering");
            return "";
        }
        if (TRACE) System.out.println("Interleaved constraints: " + ileavedConstraints);
        Map ileavedDomains = new HashMap();
        Collection nodes = new LinkedHashSet(physicalDomains.keySet());
        int i = 0;
        for (Iterator it = ileavedConstraints.iterator(); it.hasNext();) {
            Pair c = (Pair) it.next();
            Object rep1 = uf.find(c.left);
            Object rep2 = uf.find(c.right);
            if (TRACE) System.out.println("interleave constraint: " + c);
            if (TRACE) System.out.println(c.left + " rep = " + rep1);
            if (TRACE) System.out.println(c.right + " rep = " + rep2);
            if (rep1.equals(rep2)) continue;
            nodes.remove(rep1);
            nodes.remove(rep2);
            uf.union(rep1, rep2);
            Object newRep = uf.find(rep1);
            nodes.add(newRep);
            if (TRACE) System.out.println("New rep: " + newRep);
            List domains = new LinkedList();
            Object d1 = ileavedDomains.get(rep1);
            if (d1 != null) {
                domains.addAll((Collection) d1);
            } else {
                Object mapdomain = physicalDomains.get(rep1);
                domains.add(mapdomain);
            }
            Object d2 = ileavedDomains.get(rep2);
            if (d2 != null) {
                domains.addAll((Collection) d2);
            } else {
                domains.add(physicalDomains.get(rep2));
            }
            if (TRACE) System.out.println("interleaved: " + domains);
            ileavedDomains.put(newRep, domains);
        }
        beforeConstraints = updateConstraints(beforeConstraints);
        Set visited = new HashSet();
        ConstraintGraph graph = new ConstraintGraph(nodes, beforeConstraints);
        if (TRACE) System.out.println("Nodes: " + nodes);
        if (TRACE) System.out.println("Constraints: " + beforeConstraints);
        if (TRACE) System.out.println("Order graph: " + graph);
        StringBuffer sb = new StringBuffer();
        for (Collection roots = graph.getRoots(); !roots.isEmpty();) {
            if (TRACE) System.out.println("Roots: " + roots);
            for (Iterator it = roots.iterator(); it.hasNext();) {
                Object root = it.next();
                Object rep = uf.find(root);
                if (!visited.contains(rep)) {
                    sb.append((i != 0) ? "_" : "");
                    i++;
                    visited.add(rep);
                    if (TRACE) System.out.println("root: " + rep);
                    List ileaved = (List) ileavedDomains.get(rep);
                    if (ileaved != null) {
                        if (TRACE) System.out.println("interleaved");
                        Iterator jt = ileaved.iterator();
                        sb.append(jt.next());
                        while (jt.hasNext())
                            sb.append("x" + jt.next());
                    } else {
                        sb.append(physicalDomains.get(rep));
                    }
                }
                graph.removeEdgesFrom(root);
                graph.removeNode(root);
            }
            roots = graph.getRoots();
        }
        BDDSolver s = (BDDSolver) solver;
        s.VARORDER = sb.toString();
        s.setVariableOrdering();
        return sb.toString();
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.DomainAssignment#saveDomainAssignment(java.io.DataOutput)
     */
    public void saveDomainAssignment(DataOutput out) throws IOException {
        super.saveDomainAssignment(out);
        for (Iterator it = beforeConstraints.iterator(); it.hasNext();) {
            Pair c = (Pair) it.next();
            out.writeBytes(c.left+" < "+c.right+"\n");
        }
        for (Iterator it = ileavedConstraints.iterator(); it.hasNext();) {
            Pair c = (Pair) it.next();
            out.writeBytes(c.left+" ~ "+c.right+"\n");
        }
    }
}