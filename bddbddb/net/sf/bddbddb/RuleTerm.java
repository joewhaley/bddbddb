// RuleTerm.java, created Mar 16, 2004 12:42:16 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.Iterator;
import java.util.List;

/**
 * A term in a Datalog rule.
 * 
 * @author jwhaley
 * @version $Id$
 */
public class RuleTerm {
    
    /**
     * Relation for this rule term.
     */
    protected Relation relation;
    
    /**
     * List of variables in this rule term.
     */
    protected List/*<Variable>*/ variables;

    /**
     * Create a new RuleTerm with the given relation and list of variables.
     * 
     * @param variables
     * @param relation
     */
    public RuleTerm(Relation relation, List variables) {
        super();
        this.variables = variables;
        this.relation = relation;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(relation);
        sb.append("(");
        for (Iterator i = variables.iterator(); i.hasNext();) {
            sb.append(i.next());
            if (i.hasNext()) sb.append(",");
        }
        sb.append(")");
        return sb.toString();
    }

    /**
     * @return Returns the relation.
     */
    public Relation getRelation() {
        return relation;
    }

    /**
     * @return Returns the variables.
     */
    public List getVariables() {
        return variables;
    }

    /**
     * @return  number of variables in this rule term
     */
    public int numberOfVariables() {
        return variables.size();
    }

    /**
     * @param i  index
     * @return  variable at the given index
     */
    public Variable getVariable(int i) {
        return (Variable) variables.get(i);
    }

    /**
     * @param v  variable
     * @return  index of the given variable
     */
    public int getVariableIndex(Variable v) {
        return variables.indexOf(v);
    }

    /**
     * @param v  variable
     * @return  attribute of the given variable
     */
    public Attribute getAttribute(Variable v) {
        return relation.getAttribute(getVariableIndex(v));
    }
}