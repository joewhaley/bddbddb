/*
 * Created on Jul 27, 2004
 */
package net.sf.bddbddb;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import jwutil.collections.GenericMultiMap;
import jwutil.collections.MultiMap;
import jwutil.graphs.Graph;
import jwutil.graphs.Navigator;
import jwutil.graphs.SCCTopSortedGraph;
import jwutil.graphs.SCComponent;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AnonymousClassDeclaration;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.ArrayCreation;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ConditionalExpression;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.InstanceofExpression;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.ParameterizedType;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PrimitiveType;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.TypeParameter;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.WhileStatement;
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
    private String dumpPath;
    private Set paramMultiTypes = new HashSet();
    private Set fieldMultiTypes = new HashSet();
    private Set retMultiTypes = new HashSet();
    private Map/*Wrapper, SCComponent*/ typeVars2SCCs = new HashMap();
    private Map/*SCCComponent, String*/ typeVars = new HashMap();
    private Map/*ITypeBinding, TypeDeclaration*/ bindingToDecl = new HashMap();
    private MultiMap/*TypeDeclaration, String*/ classTypeVars = new GenericMultiMap();
    private Map/*String, TypeParameter*/ typeVarDecl = new HashMap();
    private PrintStream out = System.out;
    private List/*SCComponent*/ sortedTypes; 
    private Set singleTypes = new HashSet();
    
    SourceTransformation(PAFromSource p) {
        pa = p;
        dumpPath = pa.dumpPath;
        for (Iterator i = p.classes.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (o instanceof AnonymousClassDeclaration) continue;
            TypeDeclaration t = (TypeDeclaration)o;
            bindingToDecl.put(t.resolveBinding(), t);
        }
    }

    
    int counter = 0;
    
    String getNewTypeVar() {
        return "T" + String.valueOf(counter++);
    }
    
    
    String getTypeVar(Wrapper w) {
        Object scc = typeVars2SCCs.get(w);
        return (String)typeVars.get(scc);
    }
    
    
    abstract private class TransformVisitor extends ASTVisitor {
        public void postVisit(ASTNode arg0) {
            out.println(arg0);
        }
        public void preVisit(ASTNode arg0) {
            out.println(arg0);
        }
        
        ICompilationUnit icu;
        AST ast;
         
        TransformVisitor(ICompilationUnit i, AST a) {
            super(false);
            icu = i;
            ast = a;
        }
       
        private Stack/*MethodDeclaration, TypeDeclaration, AnonymousClassDeclaration*/ declStack = new Stack();
        

        ASTNode findDeclaringParent() {
            if (declStack.empty()) {
                throw new RuntimeException("ERROR empty decl stack");
            }
            return (ASTNode)declStack.peek();
        }
        
        public boolean visit(MethodDeclaration arg0) {
            declStack.add(arg0);
            return true;
        }   
        public void endVisit(MethodDeclaration arg0) {
            declStack.pop();
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
        }
        
        SimpleType toType(String tv) {
            return ast.newSimpleType(ast.newSimpleName(tv));
        }
    }
    
    
    public class RefineVisitor extends TransformVisitor {
    
        RefineVisitor(ICompilationUnit i, AST a) {
            super(i, a);
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
        
        
        public boolean visit(MethodDeclaration arg0) {
            super.visit(arg0);

            if (arg0.getBody() != null) arg0.getBody().accept(this);

            return false;
        }        
  
        public void endVisit(ClassInstanceCreation arg0) {
            TypeDeclaration decl = (TypeDeclaration)bindingToDecl.get(arg0.resolveTypeBinding());
            List tps = decl.typeParameters();
            if (tps.isEmpty()) return;
            
            Type oldtype = arg0.getType();
            // dummy type to detach teh oldtype node
            Type param = ast.newPrimitiveType(PrimitiveType.INT);
            arg0.setType(param);
            ParameterizedType pt = ast.newParameterizedType(oldtype);
            arg0.setType(pt);
            
            List tparams = pt.typeArguments();
            MultiMap mm = (MultiMap)typeVarInstantiations.get(arg0);
            out.println("mm " + mm);
            for (Iterator i = tps.iterator(); i.hasNext(); ) {
                TypeParameter tp = (TypeParameter)i.next();
                SCComponent scc = null;
                // TODO should convert to a faster solution that doesn't iterate thru the map
                for (Iterator j = typeVars.entrySet().iterator(); j.hasNext(); ) {
                    Map.Entry e = (Map.Entry)j.next();
                    if (e.getValue().equals(tp.getName().getIdentifier())) {
                        scc = (SCComponent)e.getKey();   
                        break;
                    }
                }
                
                Object[] nodes = scc.nodes();
                Collection c = new HashSet(mm.getValues(nodes[0]));
                out.println("node: " + nodes[0]);
                for (int j = 1; j < nodes.length; j++) {
                    out.println("node: " + nodes[j]);
                    c.addAll(mm.getValues(nodes[j]));
                }
                
                ITypeBinding b = null;
                for (Iterator k = c.iterator(); k.hasNext(); ) {
                    b = lub(b, (ITypeBinding)k.next());
                    out.println("lub ret " + b.getKey());
                }
                               
                if (b == null) b = pa.OBJECT.getType();
                param = toType(b.getName());
                tparams.add(param);
            }
            
            ASTNode parent = arg0.getParent();
            if (parent == null) return;
            out.println(parent.getClass());
            parent = parent.getParent();out.println(parent.getClass());
            // FIXME need to split the vds if instantiated with diff type params 
            if (parent instanceof VariableDeclarationStatement) {
                VariableDeclarationStatement vds = (VariableDeclarationStatement)parent;
                
                oldtype = vds.getType();
                // dummy type to detach teh oldtype node
                param = ast.newPrimitiveType(PrimitiveType.INT);
                vds.setType(param);
                pt = ast.newParameterizedType(oldtype);
                vds.setType(pt);
                
                List params = pt.typeArguments();
                for (Iterator j = tparams.iterator(); j.hasNext(); ) {
                    SimpleType t = (SimpleType)j.next();
                    params.add(toType(((SimpleName)(t.getName())).getIdentifier()));
                }
                
            }
            
       }
    }

    public boolean visit(VariableDeclarationStatement arg0) {
        List frags = arg0.fragments();
        if (frags.size() == 1) {
            VariableDeclarationFragment vdf = (VariableDeclarationFragment)frags.iterator().next();
            
            
            
            
            
        }
        else {
            for (Iterator i = frags.iterator(); i.hasNext(); ) {
                VariableDeclarationFragment vdf = (VariableDeclarationFragment)i.next();
                
                
            }    
        }
        
        
        return true;
  }

    
    
    private ITypeBinding lub(ITypeBinding a, ITypeBinding b) {
        out.println("lub {"+ ((a == null) ? "null" : a.getKey() )+ ", "+((b == null) ? "null" :b.getKey()) + "}");
        // theres probably a much faster alg
        if (a == null) return b;
        if (b == null) return a;
        //out.println("1");
        //if (a.getKey().equals(b.getKey())) return a;
        // TODO interfaces
        List q = new ArrayList();
        while (b != null) {
            q.add(b);
            b = b.getSuperclass();
        }
        //out.println("2");
        List p = new ArrayList();
        while (a != null) {
            p.add(a);
            a = a.getSuperclass();
        }
        //out.println("3");
        ListIterator pi = p.listIterator(p.size());
        ListIterator qi = q.listIterator(q.size());
        ITypeBinding lub = null;
        //out.println(p + " " + q);
        while (pi.hasPrevious() && qi.hasPrevious()) {
            //out.println("3.5");
            a = (ITypeBinding)pi.previous();
            b = (ITypeBinding)qi.previous();
            //out.println("4");
            if (a.getKey().equals(b.getKey())) lub = a;
            else break;
        }        
        out.println("="+lub.getKey());
        //out.println("5");
        return lub;
    }
    
    
    public class GenericizeVisitor extends TransformVisitor {        
        GenericizeVisitor(ICompilationUnit i, AST a) {
            super(i, a);
        }
        
        public boolean visit(CompilationUnit arg0) {
            arg0.recordModifications();
            return true;
        }
        
        private void addTypeVarToClass(TypeDeclaration c, Wrapper w, String declaredType) {
            Type b = null;
            if (!declaredType.equals("Object")) {
                b = toType(declaredType);
            }
            addTypeVarToClass(c, w, b);
        }
        
        private void addTypeVarToClass(TypeDeclaration c, Wrapper w, Type declaredType) {
            String tv = getTypeVar(w);  
            if (classTypeVars.contains(c, tv)) return;
            classTypeVars.add(c, tv);
            out.println("addvar: " + c + " " + tv);
            SimpleName tvname = ast.newSimpleName(tv);
            TypeParameter tp = ast.newTypeParameter();
            tp.setName(tvname);
            SCComponent scc = (SCComponent)typeVars2SCCs.get(w);
            out.println("addvar scc + " + scc);
            out.println("addvar " + scc.prev() + " exits: " + scc.next());
            if (scc.prev() == null || scc.prev().length == 0) {
                if (declaredType != null) {
                    ITypeBinding bind = declaredType.resolveBinding();
                    if (bind != null && 
                        !bind.getKey().equals(pa.OBJECT.getType().getKey())) {
                        List bounds = tp.typeBounds();
                        bounds.add(declaredType);     
                    }  
                }
            }
            else {
                List bounds = tp.typeBounds();
                SCComponent[] prev = scc.prev();
                out.println("addvar +  " + prev.length);
                for (int i = 0; i < prev.length; i++) {
                   String b = (String)typeVars.get(prev[i]);
                   bounds.add(toType(b));
                }
            }
            
            //List tparams = c.typeParameters();
            //tparams.add(tp);
            typeVarDecl.put(tv, tp);
            
        }
        
        public boolean visit(MethodDeclaration arg0) {
            super.visit(arg0);
            
            if (arg0.getBody() != null) arg0.getBody().accept(this);
            return false;
        }        
        public void endVisit(MethodDeclaration arg0) {
            super.endVisit(arg0);
            ASTNode declClass = findDeclaringParent();
            //out.println("declclass" + declClass);
            if (declClass instanceof TypeDeclaration) { // ignore anonymous classes
                //out.println("yo");
                if (retMultiTypes.contains(arg0.resolveBinding().getKey())) {
                    
                    Type oldret = arg0.getReturnType2();
                    Wrapper w = new MethodWrapper(arg0.resolveBinding());
                    arg0.setReturnType2(toType(getTypeVar(w)));                 
                    addTypeVarToClass((TypeDeclaration)declClass, w, oldret);
                }
                List params = arg0.parameters();
                for (Iterator i = params.iterator(); i.hasNext(); ) {
                    SingleVariableDeclaration svd = (SingleVariableDeclaration)i.next();
                    Type old = svd.getType();
                    if(paramMultiTypes.contains(svd.resolveBinding().getKey())) {
                        Wrapper w = new ASTNodeWrapper(svd.getName());
                        svd.setType(toType(getTypeVar(w)));                        
                        addTypeVarToClass((TypeDeclaration)declClass, w, old);
                    }
                }
            }
        }
        
        public void endVisit(FieldDeclaration arg0) {
            ASTNode declClass = findDeclaringParent();
            if (declClass instanceof TypeDeclaration) { // ignore anonymous classes
                List frags = arg0.fragments();
                Type oldType = arg0.getType();
                for (Iterator i = frags.iterator(); i.hasNext(); ) {
                    VariableDeclarationFragment vdf = (VariableDeclarationFragment)i.next();
                    if (fieldMultiTypes.contains(vdf.getName().resolveBinding().getKey())) {
                        Wrapper w = new FieldWrapper(vdf.getName());
                        SimpleType tvtype = toType(getTypeVar(w));
                        if (frags.size() == 1) {
                            arg0.setType(tvtype);
                            addTypeVarToClass((TypeDeclaration)declClass, w, oldType);
                        }
                        else { // add new field declaration
                            i.remove(); // remove this decl from this decl
                            FieldDeclaration fd = ast.newFieldDeclaration(vdf);
                            fd.setType(tvtype);
                            ((TypeDeclaration)declClass).bodyDeclarations().add(fd);
                            addTypeVarToClass((TypeDeclaration)declClass, w, 
                                ((SimpleName)(((SimpleType)oldType).getName())).getIdentifier()); // will crash if not simplename
                        }
                        
                    }
                }
            }
        }
        
        
        public void endVisit(TypeDeclaration arg0) {
            super.endVisit(arg0);
            
            List tps = arg0.typeParameters();
            Collection tvs = classTypeVars.getValues(arg0);
            out.println("endvisit typedecl : tvs "  + tvs.size() + 
                ", sortedtypes : " + sortedTypes.size());
            for (Iterator i = sortedTypes.iterator(); i.hasNext(); ) {
                Object/*String*/ tv = typeVars.get(i.next());
                if (tvs.contains(tv)) {
                    Object/*TypeParameter*/ tp = typeVarDecl.get(tv);
                    //if (tp != null) {
                    tps.add(tp);
                    //}
                }
            }
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
        //loadSingleTypes();

        Map javaASTs = pa.javaASTs;
        assignTypeVars();
        loadVarTypes(); // must be called after assigntypevars
        
        for(Iterator it = javaASTs.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry entry = (Map.Entry)it.next();
            CompilationUnit cu = (CompilationUnit)entry.getValue();
            cu.accept(new GenericizeVisitor((ICompilationUnit)entry.getKey(), 
                cu.getAST())); // add typevar decls
            cu.accept(new RefineVisitor((ICompilationUnit)entry.getKey(), 
                cu.getAST())); // refine class declarations
        }
                                                               
        
        
    }
    
    private void assignTypeVars() throws IOException {
        SubTypeGraph g = new SubTypeGraph(dumpPath + "filteredSubType.rtuples");
        Set sccs = SCComponent.buildSCC(g);
        out.println("sccs " + sccs.size());
        Set rootSCCs = new HashSet();
        for (Iterator i = sccs.iterator(); i.hasNext(); ) {
            SCComponent comp = (SCComponent)i.next();
            out.println("scc "+ comp);
            //out.println(comp.prev() + " " + comp.next());
            if (comp.prev() == null || comp.prev().length == 0) {
                rootSCCs.add(comp);            
            }
        }
        
        SCCTopSortedGraph topsortedgraph = SCCTopSortedGraph.topSort(rootSCCs);

        sortedTypes = topsortedgraph.list();
        out.println("sortedtypes size " + sortedTypes.size());
        for (Iterator i = sortedTypes.iterator(); i.hasNext(); ) {
            SCComponent comp = (SCComponent)i.next();
            String tv = getNewTypeVar();
            typeVars.put(comp, tv);
            out.println("assigned tv : " + comp + " name " + tv);
            //out.println(comp.prev() + " " + comp.next());
            Object[] w = comp.nodes();
            for (int j = 0; j < w.length; j++) {
                typeVars2SCCs.put(w[j], comp);
            }
        }
    }
    
    private Set loadSubType(String file, MultiMap subTypes) 
        throws IOException {
        Set nodes = new HashSet();
        
        BufferedReader in = 
            new BufferedReader(new FileReader(file));
        String line;
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                    
            String[] tuple = line.split("\\s");
            
            int sup = Integer.parseInt(tuple[0]);
            int sub = Integer.parseInt(tuple[1]);
            
            Wrapper supW = (Wrapper)pa.TVmap.get(sup);
            nodes.add(supW);
            if (sup == sub) continue;

            Wrapper subW = (Wrapper)pa.TVmap.get(sub);
            nodes.add(subW);
            
            subTypes.add(supW, subW);
        }        
        in.close(); 
        return nodes;
    }
    
    
    private class SubTypeGraph implements Graph {  
        private MultiMap subTypes = new GenericMultiMap();
        private Set/*Wrapper*/ nodes;
        
        /*
         * Graph nodes are: ASTNodeWrapper (for params, vars), 
         * MethodWrapper (for return values), and
         * FieldWrapper (for fields)
         */
        
        public SubTypeGraph(String file) throws IOException {
            nodes = loadSubType(file, subTypes);
        }
        
        public Collection getRoots() {
            Set roots =  new HashSet(nodes);
            //roots.removeAll(subTypes.values());
            //out.println("roots size " + roots.size());
            return roots;
        }
        
        public Navigator getNavigator() {
            return new Nav();
        }
       
        class Nav implements Navigator {
            public Collection next(Object node) {
                Collection c =  subTypes.getValues(node);
                out.println("next " + node + " : "  + c); 
                
                return (c == null) ? new ArrayList() : c;
            }

            public Collection prev(Object node) {
                Collection prevs  = new ArrayList();
                Set entrySet = subTypes.entrySet();
                for (Iterator i = entrySet.iterator(); i.hasNext(); ) {
                    Map.Entry e = (Map.Entry)i.next();
                    if (node == e.getValue()) prevs.add(e.getKey());
                }
                out.println("prev " + node + " : "  + prevs);
                return prevs;
            }   
        }
    }
    
    private Map/*ClassInstanceCreation, MultiMap<Wrapper, ITypeBinding>*/ 
        typeVarInstantiations = new HashMap(); 
     
    
    
    private void loadVarTypes() throws IOException {
        BufferedReader in = 
            new BufferedReader(new FileReader(dumpPath + "fieldTypes.rtuples"));
        String line;
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
            
            String[] tuple = line.split("\\s");
    
            int h = Integer.parseInt(tuple[0]);
            int f = Integer.parseInt(tuple[1]);
            int t = Integer.parseInt(tuple[2]);
            
            ASTNodeWrapper hw = (ASTNodeWrapper)pa.Hmap.get(h);
            MultiMap mm = (MultiMap)typeVarInstantiations.get(hw.getNode());
            if (mm == null ) {
                mm = new GenericMultiMap();
                typeVarInstantiations.put(hw.getNode(), mm); 
            }
            FieldWrapper fw = (FieldWrapper)pa.Fmap.get(f);
            TypeWrapper tw = (TypeWrapper)pa.Tmap.get(t);
            
            mm.add(fw, tw.getType());
        }        
        in.close();       
        
        in = new BufferedReader(new FileReader(dumpPath + "retTypes.rtuples"));
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
            
            String[] tuple = line.split("\\s");
            int h = Integer.parseInt(tuple[0]);
            int m = Integer.parseInt(tuple[1]);
            int t = Integer.parseInt(tuple[2]);
            
            ASTNodeWrapper hw = (ASTNodeWrapper)pa.Hmap.get(h);
            MultiMap mm = (MultiMap)typeVarInstantiations.get(hw.getNode());
            if (mm == null ) {
                mm = new GenericMultiMap();
                typeVarInstantiations.put(hw.getNode(), mm); 
            }
            MethodWrapper mw = (MethodWrapper)pa.Mmap.get(m);
            TypeWrapper tw = (TypeWrapper)pa.Tmap.get(t);
            
            mm.add(mw, tw.getType());
        }                
        in.close();  
        
        in = new BufferedReader(new FileReader(dumpPath + "argTypes.rtuples"));
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
            
            String[] tuple = line.split("\\s");
            int h = Integer.parseInt(tuple[0]);
            int v = Integer.parseInt(tuple[1]);
            int t = Integer.parseInt(tuple[2]);
            
            ASTNodeWrapper hw = (ASTNodeWrapper)pa.Hmap.get(h);
            MultiMap mm = (MultiMap)typeVarInstantiations.get(hw.getNode());
            if (mm == null ) {
                mm = new GenericMultiMap();
                typeVarInstantiations.put(hw.getNode(), mm); 
            }
            ASTNodeWrapper vw = (ASTNodeWrapper)pa.Vmap.get(v);
            TypeWrapper tw = (TypeWrapper)pa.Tmap.get(t);
            
            mm.add(vw, tw.getType());
        }        
        in.close();  
        
        
    }
    
    private void loadSingleTypes() throws IOException {
        BufferedReader in = 
            new BufferedReader(new FileReader(dumpPath + "singleType.rtuples"));
        String line;
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                    
            Wrapper wrapper = (Wrapper)pa.TVmap.get(Integer.parseInt(line.trim()));
            
            if (wrapper instanceof StringWrapper) {
                // skip
            }
            else if (wrapper instanceof ThisWrapper) {
                // skip?
            }
            else if (wrapper instanceof ASTNodeWrapper) {
                singleTypes.add(wrapper);
            }
            else throw new RuntimeException("unexpected node in singletype" + wrapper);
        }        
        in.close();               
    }
    
    private void loadMultiTypes() throws IOException {
        BufferedReader in = 
            new BufferedReader(new FileReader(dumpPath + "paramMultiType.rtuples"));
        String line;
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                    
            Wrapper wrapper = (Wrapper)pa.Vmap.get(Integer.parseInt(line.trim()));
            
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
                    
            Wrapper wrapper = (Wrapper)pa.Fmap.get(Integer.parseInt(line.trim()));
            
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
                    
            Wrapper wrapper = (Wrapper)pa.Mmap.get(Integer.parseInt(line.trim()));
            
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
