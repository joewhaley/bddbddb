/*
 * Created on Jul 23, 2004
 */
package org.sf.bddbddb;

import org.eclipse.jdt.core.dom.ITypeBinding;

/**
 * @author jimz
 */
public class TypeWrapper implements Wrapper {
    // note unlike other wrappers, this one uses binding key only 
    // for anonymous types
    // for all other types, qualified name is used

    private ITypeBinding type; // might need to switch to Type in JLS3
    
    TypeWrapper(ITypeBinding binding) {
        if (binding.isPrimitive()) {
            throw new RuntimeException("ERROR primitive type");
        }
        type = binding;
    }
    
    public String toString() {
        return /*"TYPE: " +*/ getTypeName();
    }
    
    public boolean equals(Object o) {
        if (o instanceof TypeWrapper) {
            return ((TypeWrapper)o).getTypeName().equals(getTypeName());
        }
        else if (o instanceof StringWrapper) {
            return getTypeName().equals(((StringWrapper)o).getString());
        }
        return false;
    }
    
    public int hashCode() {
        return getTypeName().hashCode();
    }
    
    public ITypeBinding getType() {
        return type;
    }
    
    public String getTypeName() {
        if (type.isAnonymous()) return type.getKey();
        return type.getQualifiedName();
    }

}
