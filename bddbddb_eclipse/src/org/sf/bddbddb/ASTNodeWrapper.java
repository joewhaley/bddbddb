package org.sf.bddbddb;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.StringLiteral;
/*
 * Created on Jul 23, 2004
 */
/**
 * @author jzhuang
 */

public class ASTNodeWrapper implements Wrapper {
    protected ASTNode n; // null for global this or implicit this
    
    ASTNodeWrapper(ASTNode obj) {
        n = obj;
        // peel off parens
        if (obj != null) { 
            n = PAFromSource.stripParens(n);
            
            if (n.getNodeType() == ASTNode.THIS_EXPRESSION 
                && !(this instanceof ThisWrapper)) {
                throw new RuntimeException("ERROR: this shouldn't be added to astnodewrapper");
            }                
        }
    }
    
    public ASTNode getNode() { return n; } 
    
    public String toString() {
        if (n == null) return "NODE: null";
        
        String s;
        if (n.getNodeType() == ASTNode.SIMPLE_NAME) {
            s = ((Name)n).resolveBinding().getKey();
            return s;
        }
        else s = n.toString();
        return "NODE: " + n.getNodeType() + ", " + s;
    }
    public boolean equals(Object o) {
        if (o instanceof ExceptionWrapper) return false;
        if (o instanceof StringWrapper) {
            switch (n.getNodeType()) {
                case ASTNode.SIMPLE_NAME:
                    String nName = ((Name) n).resolveBinding().getKey();
                    return nName.equals(((StringWrapper)o).getString());
                default:
            }
            return false;
        }
        else if (o instanceof ASTNodeWrapper) {
            ASTNodeWrapper rhs = (ASTNodeWrapper) o;
            ASTNode m = rhs.n;
            if (m == n) return true;
            if (m == null || n == null) return false;
            if (m.getAST() != n.getAST()) {
                return false;
            }
            if (m.getNodeType() != n.getNodeType()) return false;
            
            switch (m.getNodeType()) {
                case ASTNode.SUPER_METHOD_INVOCATION:
                case ASTNode.METHOD_INVOCATION:
                case ASTNode.CONDITIONAL_EXPRESSION:                    
                case ASTNode.CAST_EXPRESSION:
                case ASTNode.CLASS_INSTANCE_CREATION:
                case ASTNode.ARRAY_CREATION: 
                    return false; // since m != n
                case ASTNode.SUPER_FIELD_ACCESS:  
                case ASTNode.FIELD_ACCESS:
                case ASTNode.QUALIFIED_NAME:
                    return false; // might change in future
                case ASTNode.SIMPLE_NAME:
                    String nName = ((Name) n).resolveBinding().getKey();
                    String mName = ((Name) m).resolveBinding().getKey();
                    return nName.equals(mName);
                case ASTNode.STRING_LITERAL:
                    if (PAFromSource.UNIFY_STRING_CONSTS) {
                        String mVal = ((StringLiteral)m).getLiteralValue();
                        String nVal = ((StringLiteral)n).getLiteralValue();
                        return mVal.equals(nVal);
                    }
                    return false;
                case ASTNode.INFIX_EXPRESSION:    
                    if (((InfixExpression) m).resolveTypeBinding().isPrimitive()) {
                        throw new RuntimeException("ERROR: primitive type infix expr");
                    }
                    return false; // treated as new stmt
                case ASTNode.ASSIGNMENT:
                    if (((Assignment) m).getOperator() != Assignment.Operator.PLUS_ASSIGN
                        || ((Assignment) m).resolveTypeBinding().isPrimitive()) {
                        throw new RuntimeException("ERROR: primitive type assignment or wrong operator");
                    }
                    return false;
                case ASTNode.PARENTHESIZED_EXPRESSION:
                    throw new RuntimeException("ERROR: parens in astnodewrapper");
                    //return false;
                case ASTNode.THIS_EXPRESSION:
                    throw new RuntimeException("ERROR: this method shouldn't be called");
                    //return false;
                default:
                    System.out.println("Unhandled equals case: " + m);
            }                
            return false;
        }
        return false;
    }
    
    public int hashCode() {
        if (n == null) return 0;
        
        switch (n.getNodeType()) {
            case ASTNode.SIMPLE_NAME:
                return ((Name)n).resolveBinding().getKey().hashCode();
            case ASTNode.STRING_LITERAL:
                return ((StringLiteral)n).getLiteralValue().hashCode();
              
        }

        return n.hashCode();
    }
    
    public ITypeBinding getType() {
        if (n instanceof Expression) {
            return ((Expression)n).resolveTypeBinding();
        }
        return null;
    }
}
