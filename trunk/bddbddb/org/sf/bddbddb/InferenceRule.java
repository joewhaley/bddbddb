// InferenceRule.java, created Mar 16, 2004 12:41:14 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sf.bddbddb.ir.GenConstant;
import org.sf.bddbddb.ir.Invert;
import org.sf.bddbddb.ir.Join;
import org.sf.bddbddb.ir.JoinConstant;
import org.sf.bddbddb.ir.Project;
import org.sf.bddbddb.ir.Rename;
import org.sf.bddbddb.ir.Union;
import org.sf.bddbddb.ir.Universe;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.LinearMap;
import org.sf.bddbddb.util.MultiMap;
import org.sf.bddbddb.util.Navigator;

/**
 * InferenceRule
 * 
 * @author jwhaley
 * @version $Id$
 */
public abstract class InferenceRule implements IterationElement {
    
    List/*<RuleTerm>*/ top;
    RuleTerm bottom;
    Set/*<Variable>*/ necessaryVariables;
    Set/*<Variable>*/ unnecessaryVariables;
    boolean split;
    
    /**
     * @param top
     * @param bottom
     */
    protected InferenceRule(List/*<RuleTerm>*/ top, RuleTerm bottom) {
        super();
        this.top = top;
        this.bottom = bottom;
    }
    
    /**
     * 
     */
    void initialize() {
        calculateNecessaryVariables();
    }
    
    /**
     * @param s
     * @param terms
     * @return
     */
    static Set calculateNecessaryVariables(Collection s, List terms) {
        Set necessaryVariables = new HashSet();
        Set unnecessaryVariables = new HashSet(s);
        for (int i = 0; i < terms.size(); ++i) {
            RuleTerm rt = (RuleTerm) terms.get(i);
            for (int j = 0; j < rt.variables.size(); ++j) {
                Variable v = (Variable) rt.variables.get(j);
                if (necessaryVariables.contains(v)) continue;
                if (unnecessaryVariables.contains(v)) {
                    necessaryVariables.add(v);
                    unnecessaryVariables.remove(v);
                } else {
                    unnecessaryVariables.add(v);
                }
            }
        }
        return necessaryVariables;
    }
    
    /**
     * @return
     */
    Set calculateNecessaryVariables() {
        necessaryVariables = new HashSet();
        unnecessaryVariables = new HashSet();
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            for (int j = 0; j < rt.variables.size(); ++j) {
                Variable v = (Variable) rt.variables.get(j);
                if (necessaryVariables.contains(v)) continue;
                if (unnecessaryVariables.contains(v)) {
                    necessaryVariables.add(v);
                    unnecessaryVariables.remove(v);
                } else {
                    unnecessaryVariables.add(v);
                }
            }
        }
        
        for (int j = 0; j < bottom.variables.size(); ++j) {
            Variable v = (Variable) bottom.variables.get(j);
            if (necessaryVariables.contains(v)) continue;
            if (unnecessaryVariables.contains(v)) {
                necessaryVariables.add(v);
                unnecessaryVariables.remove(v);
            } else {
                unnecessaryVariables.add(v);
            }
        }
        return necessaryVariables;
    }
    
    /**
     * @return
     */
    public abstract boolean update();
    
    /**
     * 
     */
    public abstract void reportStats();
    
    /**
     * 
     */
    public void free() {
    }
    
    /**
     * @param rules
     * @return
     */
    public static MultiMap getRelationToUsingRule(Collection rules) {
        MultiMap mm = new GenericMultiMap();
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (o instanceof InferenceRule) {
                InferenceRule ir = (InferenceRule) o;
                for (Iterator j = ir.top.iterator(); j.hasNext(); ) {
                    RuleTerm rt = (RuleTerm) j.next();
                    mm.add(rt.relation, ir);
                }
            }
        }
        return mm;
    }
    
    /**
     * @param rules
     * @return
     */
    public static MultiMap getRelationToDefiningRule(Collection rules) {
        MultiMap mm = new GenericMultiMap();
        for (Iterator i = rules.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (o instanceof InferenceRule) {
                InferenceRule ir = (InferenceRule) o;
                mm.add(ir.bottom.relation, ir);
            }
        }
        return mm;
    }
    
    /**
     * @param myIndex
     * @param s
     * @return
     */
    public Collection/*<InferenceRule>*/ split(int myIndex, Solver s) {
        List newRules = new LinkedList();
        int count = 0;
        while (top.size() > 2) {
            RuleTerm rt1 = (RuleTerm) top.remove(0);
            RuleTerm rt2 = (RuleTerm) top.remove(0);
            if (s.TRACE) s.out.println("Combining "+rt1+" and "+rt2+" into a new rule.");
            
            // Calculate our new necessary variables.
            LinkedList ll = new LinkedList();
            ll.addAll(rt1.variables); ll.addAll(rt2.variables);
            LinkedList terms = new LinkedList(top); terms.add(bottom);
            Set myNewNecessaryVariables = calculateNecessaryVariables(ll, terms);
            
            List newTop = new LinkedList();
            newTop.add(rt1);
            newTop.add(rt2);
            // Make a new relation for the bottom.
            Map neededVariables = new LinearMap();
            Map variableOptions = new HashMap();
            Iterator i = rt1.variables.iterator();
            Iterator j = rt1.relation.attributes.iterator();
            while (i.hasNext()) {
                Variable v = (Variable) i.next();
                Attribute a = (Attribute) j.next();
                Domain d = a.attributeDomain;
                String o = a.attributeOptions;
                if (!myNewNecessaryVariables.contains(v)) continue;
                Domain d2 = (Domain) neededVariables.get(v);
                if (d2 != null && d != d2) {
                    throw new IllegalArgumentException(v+": "+d+" != "+d2);
                }
                neededVariables.put(v, d);
                String o2 = (String) variableOptions.get(v);
                if (o == null || o.equals("")) o = o2;
                if (o2 == null || o2.equals("")) o2 = o;
                if (o != null && o2 != null && !o.equals(o2)) {
                    throw new IllegalArgumentException(v+": "+o+" != "+o2);
                }
                variableOptions.put(v, o);
            }
            i = rt2.variables.iterator();
            j = rt2.relation.attributes.iterator();
            while (i.hasNext()) {
                Variable v = (Variable) i.next();
                Attribute a = (Attribute) j.next();
                Domain d = a.attributeDomain;
                String o = a.attributeOptions;
                if (!myNewNecessaryVariables.contains(v)) continue;
                Domain d2 = (Domain) neededVariables.get(v);
                if (d2 != null && d != d2) {
                    throw new IllegalArgumentException(v+": "+d+" != "+d2);
                }
                neededVariables.put(v, d);
                String o2 = (String) variableOptions.get(v);
                if (o == null || o.equals("")) o = o2;
                if (o2 == null || o2.equals("")) o2 = o;
                if (o != null && o2 != null && !o.equals(o2)) {
                    throw new IllegalArgumentException(v+": "+o+" != "+o2);
                }
                variableOptions.put(v, o);
            }
            // Make a new relation for the bottom.
            List attributes = new LinkedList();
            List newVariables = new LinkedList();
            for (i = neededVariables.entrySet().iterator(); i.hasNext(); ) {
                Map.Entry e = (Map.Entry) i.next();
                Variable v = (Variable) e.getKey();
                Domain d = (Domain) e.getValue();
                String o = (String) variableOptions.get(v);
                Attribute a = new Attribute("_"+v, d, o);
                attributes.add(a);
                newVariables.add(v);
            }
            String relationName = bottom.relation.name+"_"+myIndex+"_"+count;
            if (s.TRACE) s.out.println("New attributes: "+attributes);
            Relation newRelation = s.createRelation(relationName, attributes);
            if (s.TRACE) s.out.println("New relation: "+newRelation);
            Object o = s.nameToRelation.put(newRelation.name, newRelation);
            Assert._assert(o == null);
            RuleTerm newBottom = new RuleTerm(newVariables, newRelation);
            InferenceRule newRule = s.createInferenceRule(newTop, newBottom);
            if (s.TRACE) s.out.println("New rule: "+newRule);
            newRule.calculateNecessaryVariables();
            if (s.TRACE) s.out.println("Necessary variables: "+newRule.necessaryVariables);
            //s.rules.add(newRule);
            newRules.add(newRule);
            newRule.copyOptions(this);
            // Now include the bottom of the new rule on the top of our rule.
            top.add(0, newBottom);
            // Reinitialize this rule because the terms have changed.
            this.calculateNecessaryVariables();
            if (s.TRACE) s.out.println("Current rule is now: "+this);
            if (s.TRACE) s.out.println("My new necessary variables: "+necessaryVariables);
            Assert._assert(necessaryVariables.equals(myNewNecessaryVariables));
            ++count;
        }
        return newRules;
    }
    
    /**
     * @param mm
     * @param c
     */
    static void retainAll(MultiMap mm, Collection c) {
        for (Iterator i = mm.keySet().iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (!c.contains(o)) {
                i.remove();
                continue;
            }
            Collection vals = mm.getValues(o);
            for (Iterator j = vals.iterator(); j.hasNext(); ) {
                Object o2 = j.next();
                if (!c.contains(o2)) {
                    j.remove();
                }
            }
            if (vals.isEmpty()) i.remove();
        }
    }
    
    /**
     * @param mm
     * @param c
     */
    static void removeAll(MultiMap mm, Collection c) {
        for (Iterator i = mm.keySet().iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (c.contains(o)) {
                i.remove();
                continue;
            }
            Collection vals = mm.getValues(o);
            for (Iterator j = vals.iterator(); j.hasNext(); ) {
                Object o2 = j.next();
                if (c.contains(o2)) {
                    j.remove();
                }
            }
            if (vals.isEmpty()) i.remove();
        }
    }
    
    /**
     * @param r
     */
    public void copyOptions(InferenceRule r) {
        // No options to copy.
    }
    
    public static class DependenceNavigator implements Navigator {

        MultiMap relationToUsingRule;
        MultiMap relationToDefiningRule;
        
        public DependenceNavigator(Collection/*<InferenceRule>*/ rules) {
            this(getRelationToUsingRule(rules), getRelationToDefiningRule(rules));
        }
        
        public void retainAll(Collection c) {
            InferenceRule.retainAll(relationToUsingRule, c);
            InferenceRule.retainAll(relationToDefiningRule, c);
        }
        
        public void removeAll(Collection c) {
            InferenceRule.removeAll(relationToUsingRule, c);
            InferenceRule.removeAll(relationToDefiningRule, c);
        }
        
        public void removeEdge(Object from, Object to) {
            if (from instanceof InferenceRule) {
                InferenceRule ir = (InferenceRule) from;
                Relation r = (Relation) to;
                relationToDefiningRule.remove(r, ir);
            } else {
                Relation r = (Relation) from;
                InferenceRule ir = (InferenceRule) to;
                relationToUsingRule.remove(r, ir);
            }
        }
        
        public DependenceNavigator(DependenceNavigator that) {
            this(((GenericMultiMap)that.relationToUsingRule).copy(),
                 ((GenericMultiMap)that.relationToDefiningRule).copy());
        }
        
        /**
         * @param relationToUsingRule
         * @param relationToDefiningRule
         */
        private DependenceNavigator(MultiMap relationToUsingRule,
                                   MultiMap relationToDefiningRule) {
            super();
            this.relationToUsingRule = relationToUsingRule;
            this.relationToDefiningRule = relationToDefiningRule;
        }
        
        /* (non-Javadoc)
         * @see joeq.Util.Graphs.Navigator#next(java.lang.Object)
         */
        public Collection next(Object node) {
            if (node instanceof InferenceRule) {
                InferenceRule ir = (InferenceRule) node;
                if (relationToDefiningRule.contains(ir.bottom.relation, ir))
                    return Collections.singleton(ir.bottom.relation);
                else
                    return Collections.EMPTY_SET;
            } else {
                Relation r = (Relation) node;
                Collection c = relationToUsingRule.getValues(r);
                return c;
            }
        }

        /* (non-Javadoc)
         * @see joeq.Util.Graphs.Navigator#prev(java.lang.Object)
         */
        public Collection prev(Object node) {
            if (node instanceof InferenceRule) {
                InferenceRule ir = (InferenceRule) node;
                List list = new LinkedList();
                for (Iterator i = ir.top.iterator(); i.hasNext(); ) {
                    RuleTerm rt = (RuleTerm) i.next();
                    if (relationToUsingRule.contains(rt.relation, ir))
                        list.add(rt.relation);
                }
                return list;
            } else {
                Relation r = (Relation) node;
                Collection c = relationToDefiningRule.getValues(r);
                return c;
            }
        }
        
    }
    
    Relation generate1(Solver solver, List ir, RuleTerm rt) {
        Relation top_r = rt.relation;
        Collection varsToProject = new LinkedList(rt.variables);
        varsToProject.removeAll(necessaryVariables);
        if (!varsToProject.isEmpty()) {
            if (solver.TRACE)
                solver.out.println("Projecting away variables: "+varsToProject);
            List newAttributes = new LinkedList();
            for (int j = 0; j < rt.numberOfVariables(); ++j) {
                Variable v = rt.getVariable(j);
                if (!varsToProject.contains(v)) {
                    newAttributes.add(top_r.getAttribute(j));
                } else if (v instanceof Constant) {
                    Relation new_r = top_r.copy();
                    new_r.initialize();
                    Attribute a = top_r.getAttribute(j);
                    long value = ((Constant) v).value;
                    JoinConstant jc = new JoinConstant(new_r, top_r, a, value);
                    if (solver.TRACE)
                        solver.out.println("Generated: "+jc);
                    ir.add(jc);
                    top_r = new_r;
                }
            }
            Relation new_r = solver.createRelation(top_r+"_p", newAttributes);
            new_r.initialize();
            Project p = new Project(new_r, top_r);
            if (solver.TRACE)
                solver.out.println("Generated: "+p);
            ir.add(p);
            top_r = new_r;
        }
        return top_r;
    }
    
    public List generateIR(Solver solver) {
        List ir = new LinkedList();
        Relation result = null;
        Map varToAttrib = new HashMap();
        for (Iterator i = top.iterator(); i.hasNext(); ) {
            RuleTerm rt = (RuleTerm) i.next();

            // Step 1: Project away unnecessary variables and restrict constants.
            Relation r = generate1(solver, ir, rt);
            
            // Calculate renames.
            List newAttributes = new LinkedList();
            Map renames = new LinearMap();
            for (int j = 0; j < rt.numberOfVariables(); ++j) {
                Variable v = rt.getVariable(j);
                if (unnecessaryVariables.contains(v)) continue;
                Attribute a = rt.relation.getAttribute(j);
                Attribute a2 = (Attribute) varToAttrib.get(v);
                if (a2 == null) {
                    if (result != null && result.attributes.contains(a)) {
                        // Attribute is already present in result, use a different attribute.
                        a2 = new Attribute(a.attributeName+'\'', a.attributeDomain, "");
                        renames.put(a, a2);
                        a = a2;
                    }
                    varToAttrib.put(v, a2 = a);
                } else if (!a2.equals(a)) {
                    renames.put(a, a2);
                }
                newAttributes.add(a2);
            }
            if (!renames.isEmpty()) {
                //solver.out.println("Old attribute list: "+r.attributes);
                //solver.out.println("New attribute list: "+newAttributes);
                Relation new_r = solver.createRelation(r+"_r", newAttributes);
                new_r.initialize();
                Rename rename = new Rename(new_r, r, renames);
                if (solver.TRACE)
                    solver.out.println("Generated: "+rename);
                ir.add(rename);
                r = new_r;
            }
            
            if (result != null) {
                // Do a "join".
                newAttributes = new LinkedList(result.attributes);
                newAttributes.removeAll(r.attributes);
                newAttributes.addAll(r.attributes);
                Relation new_r = solver.createRelation(r+"_j", newAttributes);
                new_r.initialize();
                Join join = new Join(new_r, r, result);
                if (solver.TRACE)
                    solver.out.println("Generated: "+join);
                ir.add(join);
                result = new_r;
            } else {
                result = r;
            }
            
            if (solver.TRACE && result != null)
                solver.out.println("Result attributes after join: "+result.attributes);
            
            // Project away unnecessary attributes.
            List toProject = new LinkedList();
        outer:
            for (int k = 0; k < rt.numberOfVariables(); ++k) {
                Variable v = rt.getVariable(k);
                if (unnecessaryVariables.contains(v)) continue;
                Attribute a = (Attribute) varToAttrib.get(v);
                Assert._assert(a != null);
                if (solver.TRACE)
                    solver.out.print("Variable "+v+" Attribute "+a+": ");
                Assert._assert(result.attributes.contains(a));
                if (bottom.variables.contains(v)) {
                    if (solver.TRACE)
                        solver.out.println("variable needed for bottom");
                    continue;
                }
                Iterator j = top.iterator();
                while (j.next() != rt) ;
                while (j.hasNext()) {
                    RuleTerm rt2 = (RuleTerm) j.next();
                    if (rt2.variables.contains(v)) {
                        if (solver.TRACE)
                            solver.out.println("variable needed for future term");
                        continue outer;
                    }
                }
                if (solver.TRACE)
                    solver.out.println("Not needed anymore, projecting away");
                toProject.add(a);
            }
            
            if (!toProject.isEmpty()) {
                newAttributes = new LinkedList(result.attributes);
                newAttributes.removeAll(toProject);
                Relation result2 = solver.createRelation(result+"_p2", newAttributes);
                result2.initialize();
                Project p = new Project(result2, result);
                if (solver.TRACE)
                    solver.out.println("Generated: "+p);
                ir.add(p);
                result = result2;
            }
        }
        // Rename result to match head relation.
        Map renames = new LinearMap();
        List newAttributes = new LinkedList();
        for (int j = 0; j < bottom.numberOfVariables(); ++j) {
            Variable v = bottom.getVariable(j);
            if (unnecessaryVariables.contains(v)) continue;
            Attribute a = bottom.relation.getAttribute(j);
            Attribute a2 = (Attribute) varToAttrib.get(v);
            //solver.out.println("Variable "+v+" has attribute "+a2);
            Assert._assert(a2 != null);
            if (!a2.equals(a)) {
                renames.put(a2, a);
            }
            newAttributes.add(a);
        }
        if (!renames.isEmpty()) {
            //solver.out.println("Old attribute list: "+result.attributes);
            //solver.out.println("New attribute list: "+newAttributes);
            Relation result2 = solver.createRelation(result+"_r2", newAttributes);
            result2.initialize();
            Rename rename = new Rename(result2, result, renames);
            if (solver.TRACE)
                solver.out.println("Generated: "+rename);
            ir.add(rename);
            result = result2;
        }
        // Restrict constants.
        for (int j = 0; j < bottom.numberOfVariables(); ++j) {
            Variable v = bottom.getVariable(j);
            if (v instanceof Constant) {
                Attribute a = bottom.relation.getAttribute(j);
                long value = ((Constant) v).getValue();
                if (result == null) {
                    // Empty right-hand-side.
                    result = bottom.relation.copy();
                    result.initialize();
                    GenConstant c = new GenConstant(result, a, value);
                    if (solver.TRACE)
                        solver.out.println("Generated: "+c);
                    ir.add(c);
                } else {
                    Relation result2 = result.copy();
                    result2.initialize();
                    JoinConstant jc = new JoinConstant(result2, result, a, value);
                    if (solver.TRACE)
                        solver.out.println("Generated: "+jc);
                    ir.add(jc);
                    result = result2;
                }
            }
        }
        if (result != null) {
            // Finally, union in the result.
            Union u = new Union(bottom.relation, bottom.relation, result);
            if (solver.TRACE)
                solver.out.println("Generated: "+u);
            ir.add(u);
        } else {
            // No constants: Universal set.
            Universe u = new Universe(bottom.relation);
            if (solver.TRACE)
                solver.out.println("Generated: "+u);
            ir.add(u);
        }
        
        if (bottom.relation.negated != null) {
            // Update negated.
            Invert i = new Invert(bottom.relation.negated, bottom.relation);
            if (solver.TRACE)
                solver.out.println("Generated: "+i);
            ir.add(i);
        }
        
        return ir;
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(bottom);
        sb.append(" :- ");
        for (Iterator i = top.iterator(); i.hasNext(); ) {
            sb.append(i.next());
            if (i.hasNext()) sb.append(", ");
        }
        sb.append(".");
        return sb.toString();
    }
}
