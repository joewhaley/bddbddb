/*
 * Created on Jul 23, 2004
 */
package org.sf.bddbddb;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.Name;

/**
 * @author jzhuang
 */
public class StringWrapper implements Wrapper {
    public final static StringWrapper GLOBAL_THIS = 
        new StringWrapper("global(null)");
    public final static StringWrapper ARRAY_FIELD = 
        new StringWrapper("null");
    public final static StringWrapper DUMMY_METHOD = 
        new StringWrapper("DummyMethod");
    public final static StringWrapper OUTER_THIS_FIELD = 
        new StringWrapper("OuterThisField");
    
    
    private String name;
    
    public StringWrapper(String s) {
        name = s;
    }
    
    public String toString() {
        return /*"STRING: " +*/ name;
    }
    
    public boolean equals(Object o) {
        if (o instanceof StringWrapper) {
            return ((StringWrapper)o).name.equals(name);
        }
        else if (o instanceof TypeWrapper) {
            return ((TypeWrapper)o).getTypeName().equals(name);
        }
        else if (o instanceof MethodWrapper) {
            return ((MethodWrapper)o).getBinding().getKey().equals(name);
        }
        else if (o instanceof ThisWrapper 
            || o instanceof ExceptionWrapper) {
            return false;
        }
        else if (o instanceof ExceptionWrapper) {
            return false;
        }
        else if (o instanceof FieldWrapper) {
            return ((FieldWrapper)o).field.getKey().equals(name);
        }
        else if (o instanceof ASTNodeWrapper) {
            ASTNodeWrapper aw = (ASTNodeWrapper)o;
            ASTNode astnode = aw.getNode();
            if (astnode == null) return false;
            if (astnode.getNodeType() == ASTNode.SIMPLE_NAME) {
                return ((Name)astnode).resolveBinding().getKey().equals(name);
            }
        }
        
        return false;
    }
    
    public int hashCode() {
        return name.hashCode();
    }
    
    public String getString() {
        return name;
    }
    
    public ITypeBinding getType() {
        return null;
    }
}
