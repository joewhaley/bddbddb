/*
 * Created on Jul 27, 2004
 */
package org.sf.bddbddb;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.text.edits.UndoEdit;

/**
 * Apply source transformations using pointer analysis.
 * 
 * @author jzhuang
 */
public class SourceTransformation {


    private PAFromSource pa;
    
    public SourceTransformation(PAFromSource p) {
        pa = p;
        
    }
    
    
    //  TODO temporary stuff here
    public class TransformVisitor extends ASTVisitor {

        ICompilationUnit icu;
        AST ast;
         
        TransformVisitor(ICompilationUnit i, AST a) {
            super(false);
            icu = i;
            ast = a;
        }
         
        public boolean visit(CompilationUnit arg0) {
            arg0.recordModifications();
            return true;
        }
        public void endVisit(CompilationUnit arg0) {
            try {
                String contents = icu.getBuffer().getContents();
                Document doc = new Document(contents);
                
                TextEdit te = arg0.rewrite(doc, 
                    icu.getJavaProject().getOptions(true));
                
                UndoEdit ue = te.apply(doc);
                contents = doc.get();            
                icu.getBuffer().setContents(contents);
            } catch (JavaModelException e) {
                e.printStackTrace();
            } catch (MalformedTreeException e) {
                e.printStackTrace();
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
            
            
        }
        
        public void endVisit(TypeDeclaration arg0) {
            List tparams = arg0.typeParameters();
            
            TypeParameter tp = ast.newTypeParameter();
            tp.setName(ast.newSimpleName("T"));
            
            tparams.add(tp);
        }
        public void endVisit(SingleVariableDeclaration arg0) {
            Type oldtype = arg0.getType();
            if (oldtype.isPrimitiveType()) return;
            
            Type param = ast.newPrimitiveType(PrimitiveType.INT);
            arg0.setType(param);
            ParameterizedType pt = ast.newParameterizedType(oldtype);
            arg0.setType(pt);
            
            List tparams = pt.typeArguments();
            tparams.add(param);
            
        }
        public void endVisit(VariableDeclarationStatement arg0) {
            Type oldtype = arg0.getType();
            if (oldtype.isPrimitiveType()) return;
            
            Type param = ast.newPrimitiveType(PrimitiveType.INT);
            arg0.setType(param);
            ParameterizedType pt = ast.newParameterizedType(oldtype);
            arg0.setType(pt);
            
            List tparams = pt.typeArguments();
            tparams.add(param);   
        }
        public void endVisit(FieldDeclaration arg0) {
            Type oldtype = arg0.getType();
            if (oldtype.isPrimitiveType()) return;
            
            Type param = ast.newPrimitiveType(PrimitiveType.INT);
            arg0.setType(param);
            ParameterizedType pt = ast.newParameterizedType(oldtype);
            arg0.setType(pt);
            
            List tparams = pt.typeArguments();
            tparams.add(param);
        }

        public void endVisit(ClassInstanceCreation arg0) {
            Type oldtype = arg0.getType();            
            Type param = ast.newPrimitiveType(PrimitiveType.INT);
            arg0.setType(param);
            ParameterizedType pt = ast.newParameterizedType(oldtype);
            arg0.setType(pt);
            
            List tparams = pt.typeArguments();
            tparams.add(param);
        }
        public void endVisit(VariableDeclarationFragment arg0) {
            Expression e = arg0.getInitializer();
            if (e != null && e.getNodeType() == ASTNode.CAST_EXPRESSION) {
                CastExpression cast = (CastExpression)e;
                e = cast.getExpression();
                cast.setExpression(ast.newNullLiteral());
                arg0.setInitializer(e);
            }
        }
    }
    
    public void test() {
        Map javaASTs = pa.javaASTs;
        
        for(Iterator it = javaASTs.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry entry = (Map.Entry)it.next();
            CompilationUnit cu = (CompilationUnit)entry.getValue();
            cu.accept(new TransformVisitor((ICompilationUnit)entry.getKey(), 
                cu.getAST()));
        }
                                                               
        
        
    }
}
