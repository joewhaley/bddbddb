// IterationFlowGraph.java, created Jun 29, 2004
// Copyright (C) 2004 Michael Carbin
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import jwutil.collections.GenericMultiMap;
import jwutil.collections.HashWorklist;
import jwutil.collections.MultiMap;
import jwutil.collections.Pair;
import jwutil.graphs.SCComponent;
import net.sf.bddbddb.Stratify.PDGRuleNode;

/**
 * IterationFlowGraph
 * 
 * @author mcarbin
 * @version $Id$
 */
public class IterationFlowGraph {
    IterationList iterationElements;
    Map innerSccs;
    List strata, rules, loops;
    MultiMap containedBy;
    MultiMap dependencies;

    public IterationFlowGraph(List rules, Stratify strat) {
        this(rules, strat.strata, strat.innerSccs);
    }
    
    public IterationFlowGraph(List rules, List strata, Map innerSccs) {
        this.strata = strata;
        this.innerSccs = innerSccs;
        this.rules = rules;
        dependencies = new GenericMultiMap();
        loops = new LinkedList();
        iterationElements = new IterationList(false);
        containedBy = new GenericMultiMap();
        constructStrataLoops();
        constructDependencies();
    }

    private void constructStrataLoops() {
        int k = 0;
        for (Iterator it = strata.iterator(); it.hasNext(); ) {
            List stratum = (List) it.next();
            IterationList loop = buildIterationList(stratum, false);
            iterationElements.addElement(loop);
        }
    }

    private void constructDependencies() {
        constructRuleDependencies();
        constructListDependencies(iterationElements);
    }

    private void constructRuleDependencies() {
        InferenceRule.DependenceNavigator depNav = new InferenceRule.DependenceNavigator(rules);
        HashWorklist w = new HashWorklist(true);
        for (Iterator it = rules.iterator(); it.hasNext();) {
            Object rule = it.next();
            w.add(new Pair(rule, rule));
        }
        //transitive closure
        while (!w.isEmpty()) {
            Pair pair = (Pair) w.pull();
            Object link = pair.get(0);
            Object initRule = pair.get(1);
            Collection usedRelations = depNav.prev(link);
            for (Iterator it2 = usedRelations.iterator(); it2.hasNext();) {
                Collection definingRules = depNav.prev(it2.next());
                for (Iterator it3 = definingRules.iterator(); it3.hasNext();) {
                    Object o = it3.next();
                    dependencies.add(initRule, o);
                    w.add(new Pair(o, initRule));
                }
            }
        }
    }

    private void constructListDependencies(IterationList list) {
        for (Iterator it = list.iterator(); it.hasNext();) {
            IterationElement elem = (IterationElement) it.next();
            if (elem instanceof InferenceRule) {
                Collection ruleDepends = dependencies.getValues(elem);
                for (Iterator it2 = ruleDepends.iterator(); it2.hasNext();) {
                    IterationElement elem2 = (IterationElement) it2.next();
                    //nothing
                }
            } else if (elem instanceof IterationList) {
                constructListDependencies((IterationList) elem);
                Collection listDepends = dependencies.getValues(elem);
                for (Iterator it2 = listDepends.iterator(); it2.hasNext();) {
                    IterationElement elem2 = (IterationElement) it2.next();
                    //nothing
                }
            }
        }
    }

    IterationList buildIterationList(List sccList, boolean isLoop) {
        IterationList list = new IterationList(isLoop);
        for (Iterator a = sccList.iterator(); a.hasNext(); ) {
            SCComponent scc = (SCComponent) a.next();
            List c = (List) innerSccs.get(scc);
            if (c == null || c.isEmpty()) {
                IterationList list2;
                if (!isLoop && scc.isLoop()) {
                    list2 = new IterationList(true);
                    list.addElement(list2);
                } else {
                    list2 = list;
                }
                for (Iterator it = scc.nodeSet().iterator(); it.hasNext(); ) {
                    Object o = it.next();
                    if (o instanceof PDGRuleNode) {
                        InferenceRule r = ((PDGRuleNode)o).rule;
                        if (r != null) {
                            list2.addElement(r);
                            containedBy.add(r, list2);
                            if (list != list2)
                                containedBy.add(r, list);
                        }
                    }
                }
            } else {
                IterationList childLoop = buildIterationList(c, scc.isLoop());
                list.addElement(childLoop);
                Collection childElems = childLoop.getAllNestedElements();
                for (Iterator it2 = childElems.iterator(); it2.hasNext();) {
                    containedBy.add(it2.next(), list);
                }
            }
        }
        return list;
    }

    public String toString() {
        return iterationElements.toString();
    }

    public boolean dependsOn(IterationElement e1, IterationElement e2) {
        return dependencies.getValues(e1).contains(e2);
    }

    public IterationList getIterationList() {
        return iterationElements;
    }

    public IterationList expand() {
        if (iterationElements.isLoop()) {
            IterationList unrolled = iterationElements.unroll();
            iterationElements.expandInLoop();
            unrolled.elements.add(iterationElements);
            iterationElements = unrolled;
        } else {
            iterationElements.expand(true);
        }
        return iterationElements;
    }

    /**
     * @return Returns the loops.
     */
    public List getLoops() {
        return loops;
    }
    
    public IterationElement getIterationElement(String s) {
        return iterationElements.getElement(s);
    }
}
