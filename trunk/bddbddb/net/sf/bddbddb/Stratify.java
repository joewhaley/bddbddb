// Stratify.java, created May 20, 2005 2:09:33 AM by joewhaley
// Copyright (C) 2005 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import jwutil.collections.BinHeapPriorityQueue;
import jwutil.graphs.Navigator;
import jwutil.graphs.ReverseNavigator;
import jwutil.graphs.SCComponent;
import jwutil.graphs.Traversals;
import jwutil.util.Assert;

/**
 * Implements stratification and decides iteration order.
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Stratify {
    
    public Solver solver;
    public List strata;
    public Map innerSccs;
    Map nodes;
    PDGRelationNode emptyRelationNode;
    boolean NOISY;
    boolean TRACE;
    
    public Stratify(Solver solver) {
        this.solver = solver;
        this.NOISY = solver.NOISY;
        this.TRACE = solver.TRACE;
        this.nodes = new HashMap();
        this.emptyRelationNode = getRelationNode(null);
    }
    
    static class PDGRelationNode {
        Relation relation;
        List/*<PDGRuleNode>*/ in;
        List/*<PDGRuleNode>*/ out;
        
        PDGRelationNode(Relation r) {
            this.relation = r;
            this.in = new LinkedList();
            this.out = new LinkedList();
        }
        
        private static Set getRules(List list) {
            Set result = new LinkedHashSet(list.size());
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                PDGRuleNode e = (PDGRuleNode) i.next();
                if (e.rule != null)
                    result.add(e.rule);
            }
            return result;
        }
        
        Set getInRules() {
            return getRules(in);
        }
        
        Set getOutRules() {
            return getRules(out);
        }
        
        void remove() {
            for (Iterator i = in.iterator(); i.hasNext(); ) {
                PDGRuleNode e = (PDGRuleNode) i.next();
                e.to.remove(this);
                i.remove();
            }
            for (Iterator i = out.iterator(); i.hasNext(); ) {
                PDGRuleNode e = (PDGRuleNode) i.next();
                e.from.remove(this);
                i.remove();
            }
        }
        
        public String toString() {
            return relation == null ? "<null>" : relation.toString();
        }
        
    }
    
    static class PDGRuleNode {
        InferenceRule rule;
        List/*<PDGRelationNode>*/ from; // rhs
        List/*<PDGRelationNode>*/ to;   // lhs
        List/*<Boolean>*/ negated;
        
        PDGRuleNode(InferenceRule rule, List from, List to) {
            this.rule = rule;
            this.from = from;
            this.to = to;
            //Assert._assert(rule == null || from.size() == rule.top.size());
            for (Iterator i = from.iterator(); i.hasNext(); ) {
                PDGRelationNode n = (PDGRelationNode) i.next();
                n.out.add(this);
            }
            for (Iterator i = to.iterator(); i.hasNext(); ) {
                PDGRelationNode n = (PDGRelationNode) i.next();
                n.in.add(this);
            }
            if (false && rule != null) {
                negated = new ArrayList(rule.top.size());
                for (Iterator i = rule.top.iterator(); i.hasNext(); ) {
                    RuleTerm rt = (RuleTerm) i.next();
                    Boolean b;
                    if (rt.relation.name.startsWith("!"))
                        b = Boolean.TRUE;
                    else
                        b = Boolean.FALSE;
                    negated.add(b);
                }
            }
        }
        
        void remove() {
            for (Iterator i = from.iterator(); i.hasNext(); ) {
                PDGRelationNode n = (PDGRelationNode) i.next();
                n.out.remove(this);
                i.remove();
            }
            for (Iterator i = to.iterator(); i.hasNext(); ) {
                PDGRelationNode n = (PDGRelationNode) i.next();
                n.in.remove(this);
                i.remove();
            }
        }
        
        boolean isNegated(Relation n) {
            if (rule == null) return false;
            for (Iterator i = rule.top.iterator(); i.hasNext(); ) {
                RuleTerm rt = (RuleTerm) i.next();
                Relation r2 = rt.relation;
                if (r2.name.startsWith("!")) {
                    if (r2.negated == n)
                        return true;
                }
            }
            return false;
        }
        
        public String toString() {
            return ""+rule;
        }
    }
    
    PDGRelationNode getRelationNode(Relation r) {
        if (r != null && r.name.startsWith("!")) {
            Assert._assert(r.negated != null, r.name);
            r = r.negated;
        }
        PDGRelationNode p = (PDGRelationNode) nodes.get(r);
        if (p == null) {
            nodes.put(r, p = new PDGRelationNode(r));
        }
        return p;
    }
    
    PDGRuleNode getRuleNode(InferenceRule rule) {
        PDGRuleNode p = (PDGRuleNode) nodes.get(rule);
        if (p == null) {
            List from;
            if (rule.top.isEmpty()) {
                from = new ArrayList(1); from.add(emptyRelationNode);
            } else {
                from = new ArrayList(rule.top.size());
                for (Iterator i = rule.top.iterator(); i.hasNext(); ) {
                    RuleTerm rt = (RuleTerm) i.next();
                    PDGRelationNode n = getRelationNode(rt.relation);
                    from.add(n);
                }
            }
            Assert._assert(!rule.bottom.relation.name.startsWith("!"));
            PDGRelationNode n = getRelationNode(rule.bottom.relation);
            List to = new ArrayList(1); to.add(n);
            if (rule.extraDefines != null) {
                for (Iterator i = rule.extraDefines.iterator(); i.hasNext(); ) {
                    Relation r = (Relation) i.next();
                    PDGRelationNode node = getRelationNode(r);
                    to.add(node);
                }
            }
            p = new PDGRuleNode(rule, from, to);
            if (TRACE) {
                solver.out.println("Added PDG edges from "+from+" to "+to);
            }
            nodes.put(rule, p);
        }
        return p;
    }
    
    static class PDGRelationNavigator implements Navigator {

        static final PDGRelationNavigator INSTANCE = new PDGRelationNavigator();
        
        private PDGRelationNavigator() {}
        
        public Collection next(Object node) {
            PDGRelationNode n = (PDGRelationNode) node;
            List out = new ArrayList(n.out.size());
            for (Iterator i = n.out.iterator(); i.hasNext(); ) {
                PDGRuleNode e = (PDGRuleNode) i.next();
                out.addAll(e.to);
            }
            return out;
        }

        public Collection prev(Object node) {
            PDGRelationNode n = (PDGRelationNode) node;
            List in = new ArrayList(n.in.size());
            for (Iterator i = n.in.iterator(); i.hasNext(); ) {
                PDGRuleNode e = (PDGRuleNode) i.next();
                in.addAll(e.from);
            }
            return in;
        }
        
    }
    
    static boolean containsAny(Collection c1, Collection c2) {
        for (Iterator i = c2.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (c1.contains(o)) return true;
        }
        return false;
    }
    
    static class PDGEdgeNavigator implements Navigator {

        static final PDGEdgeNavigator INSTANCE = new PDGEdgeNavigator();
        
        Collection limitRelationNodes;
        Collection cutRuleNodes;
        
        private PDGEdgeNavigator() {}
        
        PDGEdgeNavigator(Collection limit, Collection edges) {
            limitRelationNodes = limit;
            cutRuleNodes = edges;
        }
        
        public Collection next(Object node) {
            if (node instanceof PDGRelationNode) {
                PDGRelationNode n = (PDGRelationNode) node;
                Assert._assert(limitRelationNodes == null || limitRelationNodes.contains(n));
                if (limitRelationNodes == null) return n.out;
                else {
                    List out = new ArrayList(n.out.size());
                    for (Iterator i = n.out.iterator(); i.hasNext(); ) {
                        PDGRuleNode e = (PDGRuleNode) i.next();
                        if (containsAny(e.to, limitRelationNodes))
                            out.add(e);
                    }
                    return out;
                }
            } else {
                PDGRuleNode e = (PDGRuleNode) node;
                if (cutRuleNodes != null && cutRuleNodes.contains(e))
                    return Collections.EMPTY_SET;
                if (limitRelationNodes != null) {
                    ArrayList result = new ArrayList(e.to.size());
                    for (Iterator i = e.to.iterator(); i.hasNext(); ) {
                        PDGRelationNode n = (PDGRelationNode) i.next();
                        if (limitRelationNodes.contains(n))
                            result.add(n);
                    }
                    return result;
                }
                return e.to;
            }
        }

        public Collection prev(Object node) {
            if (node instanceof PDGRelationNode) {
                PDGRelationNode n = (PDGRelationNode) node;
                Assert._assert(limitRelationNodes == null || limitRelationNodes.contains(n));
                if (limitRelationNodes == null && cutRuleNodes == null) return n.in;
                else {
                    List in = new ArrayList(n.in.size());
                    for (Iterator i = n.in.iterator(); i.hasNext(); ) {
                        PDGRuleNode e = (PDGRuleNode) i.next();
                        if (cutRuleNodes.contains(e))
                            continue;
                        if (containsAny(e.from, limitRelationNodes))
                            in.add(e);
                    }
                    return in;
                }
            } else {
                PDGRuleNode e = (PDGRuleNode) node;
                if (limitRelationNodes != null) {
                    ArrayList result = new ArrayList(e.from.size());
                    for (Iterator i = e.from.iterator(); i.hasNext(); ) {
                        PDGRelationNode n = (PDGRelationNode) i.next();
                        if (limitRelationNodes.contains(n))
                            result.add(n);
                    }
                    return result;
                }
                return e.from;
            }
        }
        
    }
    
    public void stratify() {
        Iterator i;
        Set inputs = new HashSet();
        inputs.addAll(solver.relationsToLoad);
        inputs.addAll(solver.relationsToLoadTuples);
        for (i = solver.getComparisonRelations().iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            inputs.add(r);
            if (r.getNegated() != null) inputs.add(r.getNegated());
            Assert._assert(!r.name.startsWith("!"));
        }
        Set outputs = new HashSet();
        outputs.addAll(solver.relationsToDump);
        outputs.addAll(solver.relationsToDumpTuples);
        outputs.addAll(solver.relationsToPrintSize);
        outputs.addAll(solver.relationsToPrintTuples);
        i = solver.dotGraphsToDump.iterator();
        while (i.hasNext()) {
            outputs.addAll(((Dot) i.next()).getUsedRelations());
        }
        stratify(solver.rules, inputs, outputs);
    }

    /**
     * Stratify the given list of rules with respect to the given inputs and outputs.
     * 
     * @param rules  rules to stratify
     * @param inputs  input relations
     * @param outputs  output relations
     */
    public void stratify(List rules, Set inputs, Set outputs) {
        // Clear any leftover from previous runs.
        nodes.clear();
        
        // Link inputs to the root emptyRelationNode.
        for (Iterator i = inputs.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            PDGRelationNode n = getRelationNode(r);
            List from = new ArrayList(1); from.add(emptyRelationNode);
            List to = new ArrayList(1); to.add(n);
            PDGRuleNode edge = new PDGRuleNode(null, from, to);
            if (TRACE) {
                solver.out.println("Added PDG edges from "+from+" to "+to);
            }
        }
        // Translate outputs from Relations to PDGRelationNodes
        Collection outputNodes = new ArrayList(outputs.size());
        for (Iterator i = outputs.iterator(); i.hasNext(); ) {
            Relation r = (Relation) i.next();
            PDGRelationNode n = getRelationNode(r);
            outputNodes.add(n);
        }
        
        // Add all edges to the PDG.
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            InferenceRule r = (InferenceRule) i.next();
            getRuleNode(r);
        }
        
        // Do a forward pass through the PDG, finding nodes that are
        // reachable from the inputs.
        List forwardRpo = Traversals.reversePostOrder(PDGRelationNavigator.INSTANCE, emptyRelationNode);
        Set reachable = new HashSet(forwardRpo);
        
        // Do a backward pass starting from the outputs.
        // Output an error if we reach a node that is not from the inputs,
        // Also, keep track of the relations we visit so we can find unnecessary relations.
        List backwardRpo = Traversals.reversePostOrder(new ReverseNavigator(PDGRelationNavigator.INSTANCE), outputNodes);
        Set unnecessary = new HashSet(solver.nameToRelation.values());
        for (Iterator i = backwardRpo.iterator(); i.hasNext(); ) {
            PDGRelationNode o = (PDGRelationNode) i.next();
            if (!reachable.remove(o)) {
                solver.out.println("ERROR: The following relation is necessary, but is not present in any strata:");
                solver.out.println("    " + o);
                solver.out.println("You may be using this relation without defining it.");
                throw new IllegalArgumentException();
            }
            if (o.relation == null) continue;
            
            boolean b = unnecessary.remove(o.relation);
            Assert._assert(b);
            if (o.relation.negated != null)
                unnecessary.remove(o.relation.negated);
        }
        
        // Output a warning if we have unused rules/relations.
        if (!unnecessary.isEmpty()) {
            if (NOISY) {
                solver.out.println("Note: the following relations are unused:");
                solver.out.println("    " + unnecessary);
            }
            Set unusedRules = new HashSet();
            for (Iterator i = unnecessary.iterator(); i.hasNext(); ) {
                Relation r = (Relation) i.next();
                PDGRelationNode n = getRelationNode(r);
                unusedRules.addAll(n.getInRules());
                unusedRules.addAll(n.getOutRules());
                n.remove();
                forwardRpo.remove(n);
            }
            if (NOISY) solver.out.println("Note: the following rules are unused:");
            for (Iterator i = unusedRules.iterator(); i.hasNext(); ) {
                InferenceRule ir = (InferenceRule) i.next();
                if (NOISY) solver.out.println("    " + ir);
                getRuleNode(ir).remove();
            }
        }
        
        // Find SCCs in the PDG.
        SCComponent root = SCComponent.buildSCC(emptyRelationNode, PDGEdgeNavigator.INSTANCE);
        
        // Topologically-sort SCCs.
        List sortedSccs = Traversals.reversePostOrder(SCComponent.SCC_NAVIGATOR, root);
        
        // Check for negated edges within any SCCs.
        for (Iterator i = sortedSccs.iterator(); i.hasNext(); ) {
            SCComponent o = (SCComponent) i.next();
            if (o.isLoop())
                checkForNegatedEdges(Arrays.asList(o.nodes()));
        }
        
        // Calculate each stratum.
        strata = new LinkedList();
        Set visitedSccs = new HashSet();
    outer:
        while (!sortedSccs.isEmpty()) {
            List stratum = discoverStratum(sortedSccs, visitedSccs);
            Assert._assert(!stratum.isEmpty());
            strata.add(stratum);
            visitedSccs.addAll(stratum);
        }
        if (NOISY) solver.out.println("Finished discovery of "+visitedSccs.size()+" SCCs in "+strata.size()+" strata");
        
        // Compute loop nesting.
        innerSccs = new HashMap();
        for (Iterator i = strata.iterator(); i.hasNext(); ) {
            Collection stratum = (Collection) i.next();
            for (Iterator j = stratum.iterator(); j.hasNext(); ) {
                SCComponent scc = (SCComponent) j.next();
                if (scc.isLoop()) {
                    computeLoopNesting(scc, new HashSet());
                }
            }
        }
    }
    
    void checkForNegatedEdges(Collection c) {
        for (Iterator i = c.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (o instanceof PDGRuleNode) {
                PDGRuleNode n = (PDGRuleNode) o;
                for (Iterator j = n.from.iterator(); j.hasNext(); ) {
                    PDGRelationNode n2 = (PDGRelationNode) j.next();
                    if (c.contains(n2) && n.isNegated(n2.relation)) {
                        solver.out.println("ERROR: Datalog is not stratifiable due to this rule:");
                        solver.out.println("    "+n.rule);
                        throw new IllegalArgumentException();
                    }
                }
            }
        }
    }
    
    List discoverStratum(List sortedSccs, Set visitedSccs) {
        if (NOISY) solver.out.println("Discovering stratum, "+visitedSccs.size()+" SCCs visited so far");
        
        List stratum = new LinkedList();
        Set stratumSet = new HashSet();
    outer:
        for (ListIterator i = sortedSccs.listIterator(); i.hasNext(); ) {
            SCComponent scc = (SCComponent) i.next();
            Assert._assert(!visitedSccs.contains(scc));
            for (int j = 0; j < scc.prevLength(); ++j) {
                SCComponent pscc = scc.prev(j);
                if (!visitedSccs.contains(pscc)) {
                    if (!stratumSet.contains(pscc)) {
                        if (TRACE) solver.out.println("Predecessor "+pscc+" of "+scc+" not done yet.");
                        continue outer;
                    }
                    if (checkForNegatedEdge(pscc, scc)) {
                        if (TRACE) solver.out.println("Negated edge: "+pscc+" to "+scc);
                        continue outer;
                    }
                } else {
                    if (TRACE) solver.out.println("Predecessor "+pscc+" of "+scc+" already visited.");
                }
            }
            if (TRACE) solver.out.println("Adding to stratum: "+scc);
            stratum.add(scc);
            boolean b = stratumSet.add(scc);
            Assert._assert(b);
            i.remove();
        }
        return stratum;
    }
    
    boolean checkForNegatedEdge(SCComponent from, SCComponent to) {
        if (to.size() == 1) {
            Object o = to.nodes()[0];
            if (o instanceof PDGRuleNode) {
                PDGRuleNode n = (PDGRuleNode) o;
                for (Iterator j = n.from.iterator(); j.hasNext(); ) {
                    PDGRelationNode n2 = (PDGRelationNode) j.next();
                    if (from.contains(n2) && n.isNegated(n2.relation)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }
    
    void computeLoopNesting(SCComponent scc, Set cutEdges) {
        if (TRACE) solver.out.println("Computing loop nesting for "+scc);
        
        scc.fillEntriesAndExits(PDGEdgeNavigator.INSTANCE);
        
        // Build a navigator just for the nodes within this SCC.
        PDGEdgeNavigator nav = new PDGEdgeNavigator(scc.nodeSet(), cutEdges);
        PDGRuleNode backEdge = chooseABackedge(scc, nav);
        if (TRACE) solver.out.println("Cutting backedge "+backEdge);
        boolean b = nav.cutRuleNodes.add(backEdge);
        Assert._assert(b);
        if (TRACE) solver.out.println("Set of cut edges: "+nav.cutRuleNodes);
        
        // Calculate inner SCCs after ignoring back edge.
        Collection entries = Arrays.asList(scc.entries());
        entries.remove(backEdge);
        Assert._assert(!entries.isEmpty());
        Collection/*<SCComponent>*/ sccs = SCComponent.buildSCC(entries, nav);
        List inner = Traversals.reversePostOrder(SCComponent.SCC_NAVIGATOR, sccs);
        if (TRACE) solver.out.println("Inner sccs for SCC"+scc.getId()+":");
        innerSccs.put(scc, inner);
        for (Iterator i = inner.iterator(); i.hasNext(); ) {
            SCComponent scc2 = (SCComponent) i.next();
            if (TRACE) solver.out.println("   "+scc2);
            if (scc2.isLoop()) {
                computeLoopNesting(scc2, (Set) nav.cutRuleNodes);
            }
        }
    }
    
    PDGRuleNode chooseABackedge(SCComponent scc, PDGEdgeNavigator nav) {
        Object[] entries = scc.entries();
        Object entry = null;
        for (int i = 0; i < entries.length; ++i) {
            entry = entries[i];
            if (!nav.cutRuleNodes.contains(entry)) break;
        }
        if (entry != null) {
            entry = scc.nodes()[0];
        }
        if (TRACE) solver.out.println("Starting from entry point "+entry);
        Assert._assert(!nav.cutRuleNodes.contains(entry));
        // find longest path.
        Set visited = new HashSet();
        BinHeapPriorityQueue queue = new BinHeapPriorityQueue();
        int priority = getPriority(entry);
        queue.insert(entry, priority);
        visited.add(entry);
        Object last = null; int min = Integer.MAX_VALUE;
        while (!queue.isEmpty()) {
            Object o = (Object) queue.peekMax();
            priority = queue.getPriority(o);
            queue.deleteMax();
            boolean any = false;
            for (Iterator i = nav.next(o).iterator(); i.hasNext(); ) {
                Object q = (Object) i.next();
                if (!scc.contains(q)) continue;
                if (visited.add(q)) {
                    queue.insert(q, priority+getPriority(q));
                    any = true;
                }
            }
            if (!any && priority <= min) {
                last = o; min = priority;
            }
        }
        if (TRACE) solver.out.println("Last node: "+last);
        Assert._assert(!nav.cutRuleNodes.contains(last));
        Object last_next;
        List possible = new LinkedList(nav.next(last));
        if (possible.size() == 1) last_next = (Object) possible.iterator().next();
        else if (possible.contains(entry)) last_next = entry;
        else {
            last_next = (Object) possible.iterator().next();
            possible.retainAll(Arrays.asList(entries));
            if (!possible.isEmpty()) last_next = (Object) possible.iterator().next();
        }
        if (TRACE) solver.out.println("Successor of last node: "+last_next);
        Assert._assert(!nav.cutRuleNodes.contains(last_next));
        if (last instanceof PDGRuleNode) {
            return (PDGRuleNode) last;
        } else {
            return (PDGRuleNode) last_next;
        }
    }
    
    public static int getPriority(Object o) {
        if (o instanceof PDGRuleNode) {
            return ((PDGRuleNode) o).rule.priority-2;
        } else {
            return ((PDGRelationNode) o).relation.priority-2;
        }
    }
    
}
