/*
 * Created on Jul 27, 2004
 */
package org.sf.bddbddb;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.text.edits.UndoEdit;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.MultiMap;

/**
 * Apply source transformations using pointer analysis.
 * 
 * @author jzhuang
 */
public class SourceTransformation {
    private PAFromSource pa;
    private String dumpPath;
    private Set paramMultiTypes = new HashSet();
    private Set fieldMultiTypes = new HashSet();
    private Set retMultiTypes = new HashSet();
    
    SourceTransformation(PAFromSource p) {
        pa = p;
        dumpPath = pa.dumpPath;
    }
    
    
    //  TODO temporary stuff here
    public class TransformVisitor extends ASTVisitor {
        int counter = 0;
        
        Stack/*MethodDeclaration, TypeDeclaration, AnonymousClassDeclaration*/ declStack = new Stack();
        
        ICompilationUnit icu;
        AST ast;
         
        TransformVisitor(ICompilationUnit i, AST a) {
            super(false);
            icu = i;
            ast = a;
        }
         
        String getNewTypeVar() {
            return "T" + String.valueOf(counter++);
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
        
        private ASTNode findDeclaringParent() {
            if (declStack.empty()) {
                throw new RuntimeException("ERROR empty decl stack");
                //return null;
            }
            
            return (ASTNode)declStack.peek();
        }
        
        private void addTypeVarToClass(TypeDeclaration c, String tv, String bound) {
            Type b = toType(bound);
            addTypeVarToClass(c, tv, b);
        }
        
        private void addTypeVarToClass(TypeDeclaration c, String tv, Type bound) {
            SimpleName tvname = ast.newSimpleName(tv);
            TypeParameter tp = ast.newTypeParameter();
            tp.setName(tvname);
            if (bound != null) {
                List bounds = tp.typeBounds();
                bounds.add(bound);
            }
            
            List tparams = c.typeParameters();
            tparams.add(tp);
        }
        
        
        private SimpleType toType(String tv) {
            return ast.newSimpleType(ast.newSimpleName(tv));
        }
        
        public boolean visit(MethodDeclaration arg0) {
            ASTNode declClass = findDeclaringParent();
            if (declClass instanceof TypeDeclaration) { // ignore anonymous classes
                if (retMultiTypes.contains(arg0.resolveBinding().getKey())) {
                    Type oldret = arg0.getReturnType2();
                    
                    String tv = getNewTypeVar();                    
                    arg0.setReturnType2(toType(tv));                 
                    addTypeVarToClass((TypeDeclaration)declClass, tv, oldret);
                }
                List params = arg0.parameters();
                for (Iterator i = params.iterator(); i.hasNext(); ) {
                    SingleVariableDeclaration svd = (SingleVariableDeclaration)i.next();
                    Type old = svd.getType();
                    if(paramMultiTypes.contains(old.resolveBinding().getKey())) {
                        String tv = getNewTypeVar();
                        svd.setType(toType(tv));                        
                        addTypeVarToClass((TypeDeclaration)declClass, tv, old);
                    }
                }
            }
            
            
            declStack.add(arg0);
            
            if (arg0.getBody() != null) arg0.getBody().accept(this);
            return false;
        }        
        public void endVisit(MethodDeclaration arg0) {
            declStack.pop();
        }
        
        public void endVisit(FieldDeclaration arg0) {
            ASTNode declClass = findDeclaringParent();
            if (declClass instanceof TypeDeclaration) { // ignore anonymous classes
                List frags = arg0.fragments();
                Type oldType = arg0.getType();
                for (Iterator i = frags.iterator(); i.hasNext(); ) {
                    VariableDeclarationFragment vdf = (VariableDeclarationFragment)i.next();
                    if (fieldMultiTypes.contains(vdf.getName().resolveBinding().getKey())) {
                        String tv = getNewTypeVar();
                        SimpleType tvtype = toType(tv);
                        if (frags.size() == 1) {
                            arg0.setType(tvtype);
                            addTypeVarToClass((TypeDeclaration)declClass, tv, oldType);
                        }
                        else { // add new field declaration
                            i.remove(); // remove this decl from this decl
                            FieldDeclaration fd = ast.newFieldDeclaration(vdf);
                            fd.setType(tvtype);
                            ((TypeDeclaration)declClass).bodyDeclarations().add(fd);
                            addTypeVarToClass((TypeDeclaration)declClass, tv, 
                                ((SimpleName)(((SimpleType)oldType).getName())).getIdentifier()); // will crash if not simplename
                        }
                        
                    }
                }
            }
      }
        
        
        public boolean visit(AnonymousClassDeclaration arg0) {
            declStack.push(arg0);
            return true;
        }
        public void endVisit(AnonymousClassDeclaration arg0) {
            declStack.pop();
        }
        
        public boolean visit(TypeDeclaration arg0) {
            declStack.push(arg0);
            return true;
        }
        public void endVisit(TypeDeclaration arg0) {
            declStack.pop();
            
//            List tparams = arg0.typeParameters();
//            
//            TypeParameter tp = ast.newTypeParameter();
//            tp.setName(ast.newSimpleName("T"));
//            
//            tparams.add(tp);
        }
        
        
        public void endVisit(SingleVariableDeclaration arg0) {
//            Type oldtype = arg0.getType();
//            if (oldtype.isPrimitiveType()) return;
//            
//            Type param = ast.newPrimitiveType(PrimitiveType.INT);
//            arg0.setType(param);
//            ParameterizedType pt = ast.newParameterizedType(oldtype);
//            arg0.setType(pt);
//            
//            List tparams = pt.typeArguments();
//            tparams.add(param);
            
        }
        public void endVisit(VariableDeclarationStatement arg0) {
//            Type oldtype = arg0.getType();
//            if (oldtype.isPrimitiveType()) return;
//            
//            Type param = ast.newPrimitiveType(PrimitiveType.INT);
//            arg0.setType(param);
//            ParameterizedType pt = ast.newParameterizedType(oldtype);
//            arg0.setType(pt);
//            
//            List tparams = pt.typeArguments();
//            tparams.add(param);   
        }


        public void endVisit(ClassInstanceCreation arg0) {
//            Type oldtype = arg0.getType();            
//            Type param = ast.newPrimitiveType(PrimitiveType.INT);
//            arg0.setType(param);
//            ParameterizedType pt = ast.newParameterizedType(oldtype);
//            arg0.setType(pt);
//            
//            List tparams = pt.typeArguments();
//            tparams.add(param);
        }
        public void endVisit(VariableDeclarationFragment arg0) {
//            Expression e = arg0.getInitializer();
//            if (e != null && e.getNodeType() == ASTNode.CAST_EXPRESSION) {
//                CastExpression cast = (CastExpression)e;
//                e = cast.getExpression();
//                cast.setExpression(ast.newNullLiteral());
//                arg0.setInitializer(e);
//            }
        }


        public void endVisit(ArrayAccess arg0) {

        }
        public void endVisit(ArrayCreation arg0) {
    
        }
        public void endVisit(ArrayInitializer arg0) {
 
        }
        public void endVisit(CatchClause arg0) {
     
        }
        public void endVisit(ConditionalExpression arg0) {
   
        }
        public void endVisit(ConstructorInvocation arg0) {
      
        }
        public void endVisit(DoStatement arg0) {

        }
        public void endVisit(ExpressionStatement arg0) {
   
        }
        public void endVisit(FieldAccess arg0) {
    
        }
        public void endVisit(ForStatement arg0) {
    
        }
        public void endVisit(IfStatement arg0) {
   
        }
        public void endVisit(InfixExpression arg0) {

        }
        public void endVisit(InstanceofExpression arg0) {
  
        }

        public void endVisit(MethodInvocation arg0) {

        }
        public void endVisit(ParenthesizedExpression arg0) {

        }
        public void endVisit(QualifiedName arg0) {
  
        }
        public void endVisit(ReturnStatement arg0) {

        }
        public void endVisit(SuperConstructorInvocation arg0) {
 
        }
        public void endVisit(SuperFieldAccess arg0) {
 
        }
        public void endVisit(SuperMethodInvocation arg0) {

        }
        public void endVisit(VariableDeclarationExpression arg0) {

        }
        public void endVisit(WhileStatement arg0) {

        }
    }
    
    public void run() throws IOException {
        loadMultiTypes();
       
        Map javaASTs = pa.javaASTs;
        
        for(Iterator it = javaASTs.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry entry = (Map.Entry)it.next();
            CompilationUnit cu = (CompilationUnit)entry.getValue();
            cu.accept(new TransformVisitor((ICompilationUnit)entry.getKey(), 
                cu.getAST()));
        }
                                                               
        
        
    }
    
    
    private void loadMultiTypes() throws IOException {
        BufferedReader in = 
            new BufferedReader(new FileReader(dumpPath + "paramMultiType.rtuples"));
        String line;
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                    
            Wrapper wrapper = (Wrapper)pa.Vmap.get(Integer.parseInt(line));
            
            if (wrapper instanceof StringWrapper) {
                // skip
            }
            else if (wrapper instanceof ThisWrapper) {
                // skip?
            }
            else if (wrapper instanceof ASTNodeWrapper) {
                paramMultiTypes.add(((Name)((ASTNodeWrapper)wrapper).getNode()).resolveBinding().getKey());
            }
            else throw new RuntimeException("unexpected node in multitype" + wrapper);
        }        
        in.close();       
        
        in = new BufferedReader(new FileReader(dumpPath + "fieldMultiType.rtuples"));
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                    
            Wrapper wrapper = (Wrapper)pa.Fmap.get(Integer.parseInt(line));
            
            if (wrapper instanceof StringWrapper) {
                // skip
            }
            else if (wrapper instanceof FieldWrapper) {
                fieldMultiTypes.add(((FieldWrapper)wrapper).getField().getKey());
            }
            else throw new RuntimeException("unexpected node in multitype" + wrapper);
        }        
        in.close();  
        
        in = new BufferedReader(new FileReader(dumpPath + "retMultiType.rtuples"));
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                    
            Wrapper wrapper = (Wrapper)pa.Mmap.get(Integer.parseInt(line));
            
            if (wrapper instanceof StringWrapper) {
                // skip
            }
            else if (wrapper instanceof MethodWrapper) {
                retMultiTypes.add(((MethodWrapper)wrapper).getBinding().getKey());
            }
            else throw new RuntimeException("unexpected node in multitype" + wrapper);
        }        
        in.close();  
    }
    
}
