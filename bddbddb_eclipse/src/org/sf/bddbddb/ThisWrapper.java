/*
 * Created on Jul 23, 2004
 */
package org.sf.bddbddb;

import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.ThisExpression;

/**
 * @author jzhuang
 */
public class ThisWrapper extends ASTNodeWrapper {
    private IMethodBinding enclosingMethod;
            
    ThisWrapper(IMethodBinding binding, ThisExpression n) {
        super(n);
        enclosingMethod = binding;
    }
    
    ThisWrapper(MethodDeclaration decl, ThisExpression n) {
        super(n);
        enclosingMethod = decl.resolveBinding();
    }
    
    public String toString() {
        return "THIS: " + enclosingMethod.getKey();
    }
    
    public boolean equals(Object o) {
        if (o instanceof ThisWrapper) {
            return enclosingMethod.getKey().equals(((ThisWrapper) o).enclosingMethod.getKey());
        }
        return false;
    }
    
    public int hashCode() { // doesn't depend on the thisexpression
        //if (method == null) return 0;
        return enclosingMethod.getKey().hashCode();
    }
    
    public ITypeBinding getType() {
        // type of this is type of class it's defined in
        return enclosingMethod.getDeclaringClass();
    }    
}
