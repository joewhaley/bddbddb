/*
 * Created on Jul 23, 2004
 */
package org.sf.bddbddb;

import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;

/**
 * @author jimz
 */
public class MethodWrapper implements Wrapper {
    private IMethodBinding method; 
    MethodWrapper(IMethodBinding binding) {
        method = binding;
    }
    
    MethodWrapper(MethodDeclaration m) {
        method = m.resolveBinding();
    }
    
    public String toString() {
        return /*"METHOD: " +*/ method.getKey();
    }
    
    public boolean equals(Object o) {
        if (o instanceof MethodWrapper) {
            return ((MethodWrapper)o).method.getKey().equals(method.getKey());
        }
        else if (o instanceof StringWrapper) {
            StringWrapper sw = (StringWrapper)o;
            return sw.getString().equals(method.getKey());
        }
        return false;
    }
    
    public int hashCode() { // doesn't depend on the thisexpression
        return method.getKey().hashCode();
    }
    
    public ITypeBinding getType() {
        throw new RuntimeException("ERROR: gettype called on methodwrapper");
        //return null;
        }

    public IMethodBinding getBinding() {
        return method;
    } 
}
