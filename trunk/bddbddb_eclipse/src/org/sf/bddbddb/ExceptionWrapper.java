/*
 * Created on Jul 23, 2004
 */
package org.sf.bddbddb;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ITypeBinding;

/**
 * @author jimz
 */
public class ExceptionWrapper extends ASTNodeWrapper {
    // Note: The type of the exception is not the type of the encapsulated ASTNode.
    private ITypeBinding type; // might need to switch to Type in JLS3
    
    ExceptionWrapper(ASTNode exception, ITypeBinding binding) {
        super(exception);
        type = binding;
    }
    
    public String toString() {
        return "EXCEPTION: " + n + " of type " + type.getQualifiedName();
    }
    
    public boolean equals(Object o) {
        if (o instanceof ExceptionWrapper) {
            ExceptionWrapper ew = (ExceptionWrapper)o;
            if (type.getKey().equals(ew.type.getKey())) {
                return super.equals(o);
            }
        }
        return false;
    }
    
    public int hashCode() { 
        return n.hashCode();
    }
    
    public ITypeBinding getType() {
        return type;
    } 
}
