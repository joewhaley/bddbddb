/*
 * Created on Aug 4, 2004
 */
package org.sf.bddbddb;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.StringLiteral;

/**
 * @author jzhuang
 */
public class FieldWrapper implements Wrapper {
    IVariableBinding field;
    
    FieldWrapper(SimpleName n) {
        //System.out.println("varbind" + n.resolveBinding().getClass());
        field = (IVariableBinding)n.resolveBinding();
    }
    
    public String toString() {
       return field.getKey();
    }
    
    public boolean equals(Object o) {
        if (o instanceof StringWrapper) {
            return field.getKey().equals(((StringWrapper)o).getString());
        }
        else if (o instanceof FieldWrapper) {
            return field.getKey().equals(((FieldWrapper)o).field.getKey());
        }
        return false;
    }
    
    public int hashCode() {
        return field.getKey().hashCode();
    }
    
    
    public ITypeBinding getType() {
        return field.getType();
    }
}
