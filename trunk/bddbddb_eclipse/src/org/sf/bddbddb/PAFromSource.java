/*
 * Created on Jun 24, 2004
 */
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AnonymousClassDeclaration;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.ArrayCreation;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.ArrayType;
import org.eclipse.jdt.core.dom.AssertStatement;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.BodyDeclaration;
import org.eclipse.jdt.core.dom.BooleanLiteral;
import org.eclipse.jdt.core.dom.BreakStatement;
import org.eclipse.jdt.core.dom.CastExpression;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.CharacterLiteral;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ConditionalExpression;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
import org.eclipse.jdt.core.dom.ContinueStatement;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.Initializer;
import org.eclipse.jdt.core.dom.InstanceofExpression;
import org.eclipse.jdt.core.dom.LabeledStatement;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.NullLiteral;
import org.eclipse.jdt.core.dom.NumberLiteral;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.PrimitiveType;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.StringLiteral;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.SynchronizedStatement;
import org.eclipse.jdt.core.dom.ThisExpression;
import org.eclipse.jdt.core.dom.ThrowStatement;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclarationStatement;
import org.eclipse.jdt.core.dom.TypeLiteral;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.WhileStatement;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.EclipseUtil;
import org.sf.bddbddb.util.ExternalAppLauncher;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.IndexedMap;
import org.sf.bddbddb.util.MultiMap;
import org.sf.bddbddb.util.NodeWrapperIndexMap;
import org.sf.bddbddb.util.SystemProperties;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;

/**
 * Derive input relations directly from source using the Eclipse AST package.
 * 
 * @author jzhuang
 */
public class PAFromSource {
    static final String IMPLICITSUPERCALL = "ImplicitSuperCall in ";
    
    public PrintStream out = System.out;
    
    static boolean TRACE_RELATIONS = !System.getProperty("pas.tracerelations", "no").equals("no");
    static boolean UNIFY_STRING_CONSTS = !System.getProperty("pas.unifystringconsts", "yes").equals("no");
    
    IndexedMap Vmap;
    IndexedMap Imap;
    IndexedMap Hmap;
    IndexedMap Fmap;
    IndexedMap Tmap;
    IndexedMap Nmap;
    IndexedMap Mmap;
    IndexedMap TVmap;
    //PathNumbering vCnumbering; // for context-sensitive
    //PathNumbering hCnumbering; // for context-sensitive
    //PathNumbering oCnumbering; // for object-sensitive
    
    TreeSet classes = new TreeSet(new Comparator() {
        public int compare(Object o1, Object o2) {        
            ITypeBinding p1;
            if (o1 instanceof TypeDeclaration) {
                p1 = ((TypeDeclaration)o1).resolveBinding();
            }
            else {
                p1 = ((AnonymousClassDeclaration)o1).resolveBinding();
            }
            ITypeBinding p2;
            if (o2 instanceof TypeDeclaration) {
                p2 = ((TypeDeclaration)o2).resolveBinding();
            }
            else {
                p2 = ((AnonymousClassDeclaration)o2).resolveBinding();
            }
            
            String n1 = p1.getKey();
            String n2 = p2.getKey();

            return n1.compareTo(n2);
        }
    });
    MultiMap initializers = new GenericMultiMap();
    
    static int bddnodes = Integer.parseInt(System.getProperty("bddnodes", "1000000"));
    static int bddcache = Integer.parseInt(System.getProperty("bddcache", "100000"));
    static BDDFactory bdd = BDDFactory.init(bddnodes, bddcache);
    
    static BDDDomain V1 = null, V2, I, H1, H2, Z, F, T1, T2, M, N, M2, TV; 
    //BDDDomain V1c[], V2c[], H1c[], H2c[];
    
    static int V_BITS=19, I_BITS=19, H_BITS=16, Z_BITS=6, F_BITS=14, T_BITS=13, N_BITS=14, M_BITS=15, TV_BITS = 19;
    //static int V_BITS=18, I_BITS=16, H_BITS=15, Z_BITS=5, F_BITS=13, T_BITS=12, N_BITS=13, M_BITS=14;
    //int VC_BITS=0, HC_BITS=0;
    //int MAX_VC_BITS = Integer.parseInt(System.getProperty("pas.maxvc", "61"));
    //int MAX_HC_BITS = Integer.parseInt(System.getProperty("pas.maxhc", "0"));

    BDD A;     // V1xV2, arguments and return values   (+context)
    BDD vP;     // V1xH1, variable points-to            (+context)
    BDD S;      // (V1xF)xV2, stores                    (+context)
    BDD L;      // (V1xF)xV2, loads                     (+context)
    BDD vT;     // V1xT1, variable type                 (no context)
    BDD hT;     // H1xT2, heap type                     (no context)
    BDD aT;     // T1xT2, assignable types              (no context)
    BDD cha;    // T2xNxM, class hierarchy information  (no context)
    BDD actual; // IxZxV2, actual parameters            (no context)
    BDD formal; // MxZxV1, formal parameters            (no context)
    BDD Iret;   // IxV1, invocation return value        (no context)
    BDD Mret;   // MxV2, method return value            (no context)
    BDD Ithr;   // IxV1, invocation thrown value        (no context)
    BDD Mthr;   // MxV2, method thrown value            (no context)
    BDD mI;     // MxIxN, method invocations            (no context)
    BDD mS;     // Mx(V1xF)xV2
    BDD mL;     // Mx(V1xF)xV2
    BDD mIE;    // MxIxM2
    BDD mvP;    // MxV1xH1
    BDD visited;// M
    //BDD mV;     // MxV, method variables                (no context)
    //BDD sync;   // V, synced locations                  (no context)

    //BDD fT;     // FxT2, field types                    (no context)
    //BDD fC;     // FxT2, field containing types         (no context)

    //BDD hP;     // H1xFxH2, heap points-to              (+context)
    BDD IE;     // IxM, invocation edges                (no context)
    BDD location2typevar;
    BDD param2typevar;
    BDD field2typevar;
    BDD ret2typevar;
    BDD concreteTypes;
    //BDD IEcs;   // V2cxIxV1cxM, context-sensitive invocation edges
    //BDD vPfilter; // V1xH1, type filter                 (no context)
    //BDD hPfilter; // H1xFxH2, type filter               (no context)
    //BDD NNfilter; // H1, non-null filter                (no context)
    //BDD IEfilter; // V2cxIxV1cxM, context-sensitive edge filter
    
    //BDDPairing V1toV2, V2toV1, H1toH2, H2toH1, V1H1toV2H2, V2H2toV1H1;
    //BDDPairing V1ctoV2c, V1cV2ctoV2cV1c, V1cH1ctoV2cV1c;
    //BDDPairing T2toT1, T1toT2;
    //BDDPairing H1toV1c[], V1ctoH1[]; 
    //BDD V1csets[], V1cH1equals[];
    static BDD V1set, V2set, H1set, T1set, T2set, Fset, Mset, M2set, Iset, Nset, Zset; //H2set, 
    static BDD V1V2set, V1Fset, V2Fset, V1FV2set, V1H1set, H1Fset; //, H2Fset, H1H2set, H1FH2set
    static BDD IMset, INset, INH1set, INT2set, T2Nset, MZset, MZVset;
    //BDD V1cset, V2cset, H1cset, H2cset, V1cV2cset, V1cH1cset, H1cH2cset;
    //BDD V1cdomain, V2cdomain, H1cdomain, H2cdomain;

    static int bddminfree = Integer.parseInt(System.getProperty("bddminfree", "20"));
    static String varorder = "N_F_I_M2_M_Z_V2xV1_T1_H2_T2_H1_TV1";//System.getProperty("bddordering"); // TODO add TV
    //int MAX_PARAMS = Integer.parseInt(System.getProperty("pas.maxparams", "4"));
    static boolean reverseLocal = System.getProperty("bddreverse", "true").equals("true"); 
    
    static {
//        if (varorder == null) {
//            // default variable orderings.
//            /*
//            if (CONTEXT_SENSITIVE || THREAD_SENSITIVE || OBJECT_SENSITIVE) {
//                if (HC_BITS > 0) {
//                    varorder = "N_F_Z_I_M2_M_T1_V2xV1_V2cxV1c_H2xH2c_T2_H1xH1c";
//                } else {
//                    //varorder = "N_F_Z_I_M2_M_T1_V2xV1_V2cxV1c_H2_T2_H1";
//                    varorder = "N_F_I_M2_M_Z_V2xV1_V2cxV1c_T1_H2_T2_H1";
//                }
//            } else if (CARTESIAN_PRODUCT && false) {
//                varorder = "N_F_Z_I_M2_M_T1_V2xV1_T2_H2xH1";
//                for (int i = 0; i < V1c.length; ++i) {
//                    varorder += "xV1c"+i+"xV2c"+i;
//                }
//            } else {
//                //varorder = "N_F_Z_I_M2_M_T1_V2xV1_H2_T2_H1";
//                varorder = "N_F_I_M2_M_Z_V2xV1_T1_H2_T2_H1";
//            } */
//            varorder = "N_F_I_M2_M_Z_V2xV1_T1_T2_H1";
//        }
//        
        
        //initBDDFactory();
    }
        
    //MultiMap constructors /*<String(class key), Name(constructor)>*/ 
                      //  = new GenericMultiMap();
    
    private static void initBDDFactory() {
        //USE_VCONTEXT = VC_BITS > 0;
        //USE_HCONTEXT = HC_BITS > 0;
        
        //if (USE_VCONTEXT || USE_HCONTEXT) 
        //  bddnodes *= 2;

        bdd.setMaxIncrease(bddnodes);
        bdd.setMinFreeNodes(bddminfree);

        V1 = makeDomain("V1", V_BITS);
        V2 = makeDomain("V2", V_BITS);
        I = makeDomain("I", I_BITS);
        H1 = makeDomain("H1", H_BITS);
        H2 = makeDomain("H2", H_BITS); // needed to make domain alloc order match joeq
        Z = makeDomain("Z", Z_BITS);
        F = makeDomain("F", F_BITS);
        T1 = makeDomain("T1", T_BITS);
        T2 = makeDomain("T2", T_BITS);
        N = makeDomain("N", N_BITS);
        M = makeDomain("M", M_BITS);
        M2 = makeDomain("M2", M_BITS);
        TV = makeDomain("TV1", TV_BITS);

        V1set = V1.set();

        V2set = V2.set();

        H1set = H1.set();

        T1set = T1.set();
        T2set = T2.set();
        Fset = F.set();
        Mset = M.set();
        M2set = M2.set();
        Nset = N.set();
        Iset = I.set();
        Zset = Z.set();

        V1V2set = V1set.and(V2set);
        V1FV2set = V1V2set.and(Fset);
        V1H1set = V1set.and(H1set);
        V1Fset = V1set.and(Fset);
        V2Fset = V2set.and(Fset);
        IMset = Iset.and(Mset);
        INset = Iset.and(Nset);
        INH1set = INset.and(H1set);
        INT2set = INset.and(T2set);
        H1Fset = H1set.and(Fset);
        //H2Fset = H2set.and(Fset);
        //H1H2set = H1set.and(H2set);
        //H1FH2set = H1Fset.and(H2set);
        T2Nset = T2set.and(Nset);
        MZset = Mset.and(Zset);
        MZVset = MZset.and(V1set);

        System.out.println("Using variable ordering "+varorder);
        int[] ordering = bdd.makeVarOrdering(reverseLocal, varorder);
        bdd.setVarOrder(ordering);
    }

    private static BDDDomain makeDomain(String name, int bits) {
        Assert._assert(bits < 64);
        BDDDomain d = bdd.extDomain(new long[] { 1L << bits })[0];
        d.setName(name);
        return d;
    }
    
    public BDD initBDD(String name) {

        try {
            String fn = loadPath+name+".bdd";
            if (new File(fn).exists()) {
                out.println("loading existing bdd " + name);
                BDD b= bdd.load(fn);
                out.println("nodes: " + b.nodeCount());
                return b;
            }
        } catch (IOException x) {
        }
        return bdd.zero();
    }
    
    private void resetBDDs() {
        A = initBDD("A");
        vP = initBDD("vP0");
        S = initBDD("S");
        L = initBDD("L");
        vT = initBDD("vT");
        hT = initBDD("hT");
        aT = initBDD("aT");
        mL = initBDD("mL");
        mS = initBDD("mS");
        mIE = initBDD("mIE");
        mvP = initBDD("mvP");
        
        actual = initBDD("actual");
        formal = initBDD("formal");
        Iret = initBDD("Iret");
        Mret = initBDD("Mret");
        Ithr = initBDD("Ithr");
        Mthr = initBDD("Mthr");
        mI = initBDD("mI");
        IE = initBDD("IE0");
        File v = new File(loadPath + "visited.bdd");
        v.delete();
        visited = initBDD("visited");
        cha = initBDD("cha");
        
        location2typevar = initBDD("location2typevar");
        param2typevar = initBDD("param2typevar");
        field2typevar = initBDD("field2typevar");
        ret2typevar = initBDD("ret2typevar");
        concreteTypes = initBDD("concreteTypes");
    }
   

    TypeWrapper CLONEABLE = null;
    TypeWrapper OBJECT = null;
    TypeWrapper SERIALIZABLE = null;
    TypeWrapper STRING = null;
        
    public static ASTNode stripParens(ASTNode n) {
        while (n.getNodeType() == ASTNode.PARENTHESIZED_EXPRESSION) {
            n = ((ParenthesizedExpression) n).getExpression();
        }
        return n;
    }
    
    /**
     * @author jzhuang
     */
    class PAASTVisitor extends ASTVisitor {
        
        final boolean useMrelations;
        final boolean generateVisited;
        
        Stack/*MethodDeclaration, TypeDeclaration, AnonymousClassDeclaration*/ declStack = new Stack();
        Stack/*StringWrapper*/ clinitStack = new Stack();
      
        public boolean visit(CompilationUnit arg0) {
            out.println("setting up visitor.");
            AST ast = arg0.getAST();
            CLONEABLE = 
                new TypeWrapper(ast.resolveWellKnownType("java.lang.Cloneable"));
            OBJECT = 
                new TypeWrapper(ast.resolveWellKnownType("java.lang.Object"));
            SERIALIZABLE = 
                new TypeWrapper(ast.resolveWellKnownType("java.io.Serializable"));
            STRING = 
                new TypeWrapper(ast.resolveWellKnownType("java.lang.String"));
            return true; 
        }
        
        // TODO handle outer this

        public PAASTVisitor(boolean l, boolean r) { 
            super(false); 
            useMrelations = l;
            generateVisited = r;
            /*this(0,0);*/
            
            if (useMrelations) addToMVP(StringWrapper.DUMMY_METHOD, 
                StringWrapper.GLOBAL_THIS, StringWrapper.GLOBAL_THIS);   
            else addToVP(StringWrapper.GLOBAL_THIS, 
                StringWrapper.GLOBAL_THIS);    
            
            if (generateVisited) addToVisited(StringWrapper.DUMMY_METHOD);
        }
        
        // vP
        public boolean visit(ArrayCreation arg0) {
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            if (useMrelations) {
                addToMVP(node, node);
            }
            else addToVP(node, node);
            return true;
        }
        public boolean visit(StringLiteral arg0) {
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            if (useMrelations) {
                addToMVP(node, node);
            }
            else addToVP(node, node);          
            return true;
        }
        public boolean visit(InfixExpression arg0) {
            return true;
        }
        public void endVisit(InfixExpression arg0) {
            if (arg0.resolveTypeBinding().isPrimitive()) return;
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            if (useMrelations) {
                addToMVP(node, node);
            }
            else addToVP(node, node);
        }
        // vP, actual, Mthr, Iret, Ithr, mI, IE0
        public boolean visit(ClassInstanceCreation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);

            IMethodBinding method = arg0.resolveConstructorBinding();
            ASTNode decl = findDeclaringParent();
            List enclosingMethods;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION || 
                decl.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) { // in an initializer
                Initializer init = getInitializer(arg0);
                if (init == null) {
                    VariableDeclaration vd = getVarDecl(arg0);
                    if (isStatic(vd.getName())) {
                        enclosingMethods = Collections.singletonList(getClinit());
                    } 
                    else {
                        enclosingMethods = getWrappedConstructors(decl);
                    }
                }
                else if (isStatic(init)) {
                    //initializers.add(decl, init);
                    enclosingMethods = Collections.singletonList(getClinit());
                }
                else {
                    enclosingMethods = getWrappedConstructors(decl);
                }
            }
            else {
                enclosingMethods = 
                    Collections.singletonList(new MethodWrapper((MethodDeclaration)decl));         
            }
            
            if (useMrelations) {
                addToMVP(enclosingMethods, n, n);
            }
            else addToVP(n, n);
            
            List thisParams = Collections.singletonList(n);
                          
            List args = arg0.arguments();
            addMethodInvocation(thisParams, n, method, args, 
                enclosingMethods, new ASTNodeWrapper(null));
            return true;
        }
        
        // A, vP
        public boolean visit(Assignment arg0) {
            arg0.getRightHandSide().accept(this);
            return false; // ignore left side
        }
        public void endVisit(Assignment arg0) {
            Expression right = arg0.getRightHandSide();  
            Expression left = arg0.getLeftHandSide();            
            ITypeBinding rType = right.resolveTypeBinding();
            if (rType == null) { 
                throw new RuntimeException("unresolved bindings");
            }
            else {
                if (rType.isPrimitive() || rType.isNullType()) return;
                // string +=
                if (arg0.getOperator() == Assignment.Operator.PLUS_ASSIGN) {
                    if (useMrelations) {
                        addToMVP(new ASTNodeWrapper(left), 
                            new ASTNodeWrapper(arg0));
                    }
                    else addToVP(new ASTNodeWrapper(left), 
                            new ASTNodeWrapper(arg0));
                }
                else compareAssignment(left, right);
            } 
        }
        
        // A, S
        public boolean visit(ConditionalExpression arg0) {
            return true; 
        }
        public void endVisit(ConditionalExpression arg0) {
            ITypeBinding type = arg0.resolveTypeBinding();
            if (type.isPrimitive() || type.isNullType()) return;  
            
            compareAssignment(arg0, arg0.getThenExpression());
            compareAssignment(arg0, arg0.getElseExpression());
        }
        public boolean visit(CastExpression arg0) {
            return true;
        }        
        public void endVisit(CastExpression arg0) {
            ITypeBinding type = arg0.resolveTypeBinding();
            if (type.isPrimitive() || type.isNullType()) return;  
            type = arg0.getExpression().resolveTypeBinding();
            if (type.isNullType()) return;  
            compareAssignment(arg0, arg0.getExpression());
        }
        public boolean visit(SingleVariableDeclaration arg0) {
            return false; // dont visit the name
        }        
        public void endVisit(SingleVariableDeclaration arg0) {
            if (arg0.getInitializer() != null) {
                if (!arg0.getType().isPrimitiveType()) {
                    compareAssignment(arg0.getName(), arg0.getInitializer());
                }
                arg0.getInitializer().accept(this);
            }   
        }
        public boolean visit(VariableDeclarationFragment arg0) {
            return false; // dont visit the name
        }
        public void endVisit(VariableDeclarationFragment arg0) {
            if (arg0.getInitializer() != null) {
                if (!arg0.resolveBinding().getType().isPrimitive()) { 
                    compareAssignment(arg0.getName(), arg0.getInitializer());
                }
                arg0.getInitializer().accept(this);
            }
        }
        
        private void compareAssignment(Expression left, Expression right) {
            // strip parens
            left = (Expression)stripParens(left);
            right = (Expression)stripParens(right);

            if (right.getNodeType() == ASTNode.ASSIGNMENT) {
                compareAssignment(left, ((Assignment) right).getLeftHandSide());
                return;
            }
            
            switch (left.getNodeType()) {
                case ASTNode.ARRAY_ACCESS:
                    Expression arr  = ((ArrayAccess)left).getArray();
                    arr.accept(this);
                    storeToQualifiedField(arr, StringWrapper.ARRAY_FIELD, right);
                    return;
                case ASTNode.SUPER_FIELD_ACCESS:
                    // TODO store to super
                    System.err.println("ERROR: super field access to be handled" + left);
                    break; 
                case ASTNode.THIS_EXPRESSION:
                    switch (right.getNodeType()) {
                        case ASTNode.CLASS_INSTANCE_CREATION:
                        case ASTNode.ARRAY_CREATION:
                        case ASTNode.STRING_LITERAL:
                        case ASTNode.INFIX_EXPRESSION:
                        case ASTNode.SIMPLE_NAME:
                        case ASTNode.QUALIFIED_NAME:   
                        case ASTNode.SUPER_FIELD_ACCESS:                       
                        case ASTNode.FIELD_ACCESS:
                        case ASTNode.CONDITIONAL_EXPRESSION:          
                        case ASTNode.METHOD_INVOCATION:
                        case ASTNode.SUPER_METHOD_INVOCATION: 
                        case ASTNode.CAST_EXPRESSION:
                        case ASTNode.ARRAY_ACCESS:
                            addThisToA((ThisExpression)left, right);
                            return;
                        case ASTNode.THIS_EXPRESSION:
                            addThisToA((ThisExpression) left, 
                                    (ThisExpression)right);
                            return;
                        default:
                            // e.g. nullexpr, do nothing
                    }
                    return;
                case ASTNode.QUALIFIED_NAME:
                    QualifiedName qa = (QualifiedName)left;
                    left = qa.getQualifier();
                    left.accept(this);
                    if (isStatic(qa.getName())) {
                        storeToStaticField(qa.getName(), right);
                    }
                    else { // treat as field access
                        storeToQualifiedField(left, qa.getName(), right);
                    }
                    return;
                case ASTNode.FIELD_ACCESS:
                    FieldAccess fa = (FieldAccess)left;
                    left = fa.getExpression();
                    left.accept(this); // to handle x.y.z = stuff;
                    SimpleName name = fa.getName();
                    if (isStatic(name)) {
                        storeToStaticField(name, right);
                    }
                    else {
                        ThisExpression t = getThis(left);
                        if (t == null) { // store
                            storeToQualifiedField(left, name, right);
                        }
                        else { // left = this 
                            storeToThisField(t, name, right);
                        }
                    }
                    return;
                case ASTNode.SIMPLE_NAME:
                    // out.println(left + " = " + right + " field? " + isField((Name)left));
                    if (isField((Name)left)) { // implicit this?
                        // store                        
                        if (isStatic((Name)left)) {
                            storeToStaticField((SimpleName)left, right);
                        }
                        else {
                            storeToThisField(null, (SimpleName)left, right);
                        }
                        return;
                    }
                    // else: not field, drop down to standard assignment case 
                default: // used for standard assign, cast, conditional exprs

                    switch (right.getNodeType()) {
                        case ASTNode.CLASS_INSTANCE_CREATION:
                        case ASTNode.ARRAY_CREATION:
                        case ASTNode.STRING_LITERAL:
                        case ASTNode.INFIX_EXPRESSION:
                        case ASTNode.SIMPLE_NAME:
                        case ASTNode.QUALIFIED_NAME:   
                        case ASTNode.SUPER_FIELD_ACCESS:                       
                        case ASTNode.FIELD_ACCESS:
                        case ASTNode.CONDITIONAL_EXPRESSION:          
                        case ASTNode.METHOD_INVOCATION:
                        case ASTNode.SUPER_METHOD_INVOCATION: 
                        case ASTNode.CAST_EXPRESSION:
                        case ASTNode.ARRAY_ACCESS:
                            addToA(left, right);  
                            return;
                        case ASTNode.THIS_EXPRESSION:
                            addThisToA(left, (ThisExpression)right);
                            return;
                        default:
                            // e.g. nullexpr, do nothing
                    }
            }
        }
         
        private void storeToThisField(ThisExpression t, 
            SimpleName field, Expression rhs) {

            switch (rhs.getNodeType()) {
                case ASTNode.CLASS_INSTANCE_CREATION:
                case ASTNode.ARRAY_CREATION:
                case ASTNode.STRING_LITERAL:
                case ASTNode.INFIX_EXPRESSION:
                case ASTNode.SIMPLE_NAME:
                case ASTNode.QUALIFIED_NAME:   
                case ASTNode.SUPER_FIELD_ACCESS:                       
                case ASTNode.FIELD_ACCESS:
                case ASTNode.CONDITIONAL_EXPRESSION:          
                case ASTNode.METHOD_INVOCATION:
                case ASTNode.SUPER_METHOD_INVOCATION: 
                case ASTNode.CAST_EXPRESSION:
                case ASTNode.ARRAY_ACCESS:
                    addToS(t, field, new ASTNodeWrapper(rhs));  
                    return;
                case ASTNode.THIS_EXPRESSION:
                    addToS(t, field, (ThisExpression)rhs);
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }
        }

        private void storeToQualifiedField(Expression qualifier, 
            SimpleName field, Expression rhs) {
            storeToQualifiedField(qualifier, new FieldWrapper(field), rhs);
        }
        
        private void storeToQualifiedField(Expression qualifier, 
            Wrapper field, Expression rhs) {

            switch (rhs.getNodeType()) {
                case ASTNode.CLASS_INSTANCE_CREATION:
                case ASTNode.ARRAY_CREATION:
                case ASTNode.STRING_LITERAL:
                case ASTNode.INFIX_EXPRESSION:
                case ASTNode.SIMPLE_NAME:
                case ASTNode.QUALIFIED_NAME:   
                case ASTNode.SUPER_FIELD_ACCESS:                       
                case ASTNode.FIELD_ACCESS:
                case ASTNode.CONDITIONAL_EXPRESSION:          
                case ASTNode.METHOD_INVOCATION:
                case ASTNode.SUPER_METHOD_INVOCATION: 
                case ASTNode.CAST_EXPRESSION:
                case ASTNode.ARRAY_ACCESS:
                    if (useMrelations) {
                        addToMS(new ASTNodeWrapper(qualifier), field, rhs);
                    }
                    else addToS(new ASTNodeWrapper(qualifier), field, 
                        new ASTNodeWrapper(rhs));  
                    return;
                case ASTNode.THIS_EXPRESSION:
                    addToS(new ASTNodeWrapper(qualifier), 
                         field, (ThisExpression)rhs);
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }
        }

       
        private void storeToStaticField(SimpleName field, Expression rhs) {
            switch (rhs.getNodeType()) {
                case ASTNode.CLASS_INSTANCE_CREATION:
                case ASTNode.ARRAY_CREATION:
                case ASTNode.STRING_LITERAL:
                case ASTNode.INFIX_EXPRESSION:
                case ASTNode.SIMPLE_NAME:
                case ASTNode.QUALIFIED_NAME:   
                case ASTNode.SUPER_FIELD_ACCESS:                       
                case ASTNode.FIELD_ACCESS:
                case ASTNode.CONDITIONAL_EXPRESSION:          
                case ASTNode.METHOD_INVOCATION:
                case ASTNode.SUPER_METHOD_INVOCATION: 
                case ASTNode.CAST_EXPRESSION:
                case ASTNode.ARRAY_ACCESS:
                    if (useMrelations) {
                        addToMS(StringWrapper.GLOBAL_THIS, new FieldWrapper(field), rhs);
                    }
                    else addToS(StringWrapper.GLOBAL_THIS, 
                        new FieldWrapper(field), new ASTNodeWrapper(rhs));  
                    return;
                case ASTNode.THIS_EXPRESSION:
                    addToS(StringWrapper.GLOBAL_THIS, 
                        new FieldWrapper(field), (ThisExpression)rhs);
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }    
        }

        // formal
        public boolean visit(MethodDeclaration arg0) {  
            declStack.push(arg0);
            
            int modifiers = arg0.getModifiers();

            int M_i = Mmap.get(new MethodWrapper(arg0));
            BDD M_bdd = M.ithVar(M_i);
            // argument 0 added in type decl node
            List params = arg0.parameters();
            Iterator it = params.iterator();
            for (int i = 1; it.hasNext(); i++) {
                SingleVariableDeclaration v = (SingleVariableDeclaration)it.next();
                if (v.getType().isPrimitiveType()) continue;
                // this pter added in type decl
                addToFormal(M_bdd, i, new ASTNodeWrapper(v.getName()));
            }
            M_bdd.free();
                        
            if (arg0.getBody() != null) {
                if (arg0.isConstructor()) {  // implicit super()?
                    List stmts = arg0.getBody().statements();
                    Statement v = (stmts.size() == 0) ? 
                                    null : (Statement)stmts.get(0);
                    if (v == null || 
                        !(v.getNodeType() == ASTNode.SUPER_CONSTRUCTOR_INVOCATION || 
                            v.getNodeType() == ASTNode.CONSTRUCTOR_INVOCATION)) {
                        ITypeBinding supClass = arg0.resolveBinding().getDeclaringClass().getSuperclass();
                        if (supClass != null) {
                            StringWrapper n = new StringWrapper(IMPLICITSUPERCALL + arg0.resolveBinding().getKey());
                            IMethodBinding[] methods =supClass.getDeclaredMethods(); 
                            IMethodBinding method = null;
                            for (int i = 0; i < methods.length; i++) {
                                if (methods[i].isConstructor() && 
                                    methods[i].getParameterTypes().length == 0) {
                                    method = methods[i];
                                    break;
                                }
                            }
                            
                            List enclosingMethods = 
                                Collections.singletonList(new MethodWrapper(arg0));
                            List thisParams = 
                                Collections.singletonList(new ThisWrapper(arg0, null));
                            List args = Collections.EMPTY_LIST;
                            
                            addMethodInvocation(thisParams, n, method, args, 
                                enclosingMethods, new ASTNodeWrapper(null));
                        }
                    }
                }
                
                arg0.getBody().accept(this);
            }
            
            return false; // do not go into the decls
        }
        public void endVisit(MethodDeclaration arg0) {
            declStack.pop();
        }

        // L
        public boolean visit(FieldAccess arg0) {
            Expression expr = arg0.getExpression();
            expr.accept(this);
            if (!arg0.resolveTypeBinding().isPrimitive()) {
                // load
                SimpleName f = arg0.getName();  
                if (isStatic(f)) {
                    if (useMrelations) {
                        addToML(StringWrapper.GLOBAL_THIS, 
                            new FieldWrapper(f), arg0);
                    }
                    else addToL(StringWrapper.GLOBAL_THIS, f, arg0);
                }
                else {
                    ThisExpression t = getThis(expr);
                    if (t != null) {
                        addToL(t, f, new ASTNodeWrapper(arg0));
                    }
                    else {
                        if (useMrelations) {
                            addToML(new ASTNodeWrapper(expr), 
                                new ASTNodeWrapper(f), arg0);
                        }
                        else addToL(new ASTNodeWrapper(expr), f, arg0);
                    }
                }
            }
            return false; // so the name isn't added as implicit this load
        }
        
        public boolean visit(SimpleName arg0) {
            //out.println("SIMPLENAME: " + arg0);
            if (arg0.resolveBinding().getKind() == IBinding.VARIABLE) {
                if (!arg0.resolveTypeBinding().isPrimitive()) {
                    if (isField(arg0)) { // load, implicit this
 
                        if (isStatic(arg0)) {
                            if (useMrelations) {
                                addToML(StringWrapper.GLOBAL_THIS, new FieldWrapper(arg0), 
                                    arg0);
                            }
                            else addToL(StringWrapper.GLOBAL_THIS, arg0, arg0);
                        }
                        else {
                            addToL(null, arg0, new ASTNodeWrapper(arg0));
                        }
                    }
                }
            }
            return false;
        }

        public boolean visit(QualifiedName arg0) {
            arg0.getQualifier().accept(this);
            if (arg0.resolveBinding().getKind() == IBinding.VARIABLE 
                && !arg0.resolveTypeBinding().isPrimitive()) {
                if (isStatic(arg0)) {
                    // load, treat as static field access
                    if (useMrelations) {
                        addToML(StringWrapper.GLOBAL_THIS, 
                            new FieldWrapper(arg0.getName()), arg0);
                    }
                    else addToL(StringWrapper.GLOBAL_THIS, arg0.getName(), arg0);
                }
                else { // treat as field
                    ThisExpression t = getThis(arg0.getQualifier());
                    if (t != null) {
                        addToL(t, arg0.getName(), new ASTNodeWrapper(arg0));
                    }
                    else {
                        if (useMrelations) {
                            addToML(new ASTNodeWrapper(arg0.getQualifier()), 
                                new ASTNodeWrapper(arg0.getName()), arg0);
                            
                        }
                        else addToL(new ASTNodeWrapper(arg0.getQualifier()), 
                            arg0.getName(), arg0);
                    }
                }
            }
            return false;
        }
        
        public boolean visit(ArrayAccess arg0) {
            return true;
        }
        public void endVisit(ArrayAccess arg0) {
   
            if (!arg0.resolveTypeBinding().isPrimitive()) {
                // load
                if (useMrelations) {
                    addToML(new ASTNodeWrapper(arg0.getArray()), 
                        StringWrapper.ARRAY_FIELD, arg0);
                }
                else addToL(new ASTNodeWrapper(arg0.getArray()), 
                        StringWrapper.ARRAY_FIELD, new ASTNodeWrapper(arg0));
            }
        }
        
        // aT, formal
        public boolean visit(AnonymousClassDeclaration arg0) {
            ITypeBinding classBinding = arg0.resolveBinding();
            addClass(arg0, classBinding);
            return true;
        }
        
        public void endVisit(AnonymousClassDeclaration arg0) {
            declStack.pop();
            clinitStack.pop();
        }
        
        public boolean visit(TypeDeclaration arg0) {
            ITypeBinding classBinding = arg0.resolveBinding();
            addClass(arg0, classBinding);
            return true;
        }

        private void addClass(ASTNode arg0, ITypeBinding classBinding) {
            clinitStack.push(new StringWrapper(classBinding.getKey() + ".<clinit>"));
            if (generateVisited) {
                addToVisited(getClinit());
            }
            
            declStack.push(arg0);
            classes.add(arg0);
            
            // do aT last, more expensive but more accurate when 
            // source isn't available for libraries. 
            //addBindingToAT(classBinding); 
            
            boolean outerthis = hasOuterThis(classBinding);
            IMethodBinding[] bindings = classBinding.getDeclaredMethods();
            for (int i = 0; i < bindings.length; i++) {
                IMethodBinding binding = bindings[i];
                Wrapper thisParam;
                if (isStatic(binding)) {
                    thisParam = StringWrapper.GLOBAL_THIS;
                }
                else {
                    thisParam = new ThisWrapper(binding, null);
                }
                
                int M_i = Mmap.get(new MethodWrapper(binding));
                BDD M_bdd = M.ithVar(M_i);
                addToFormal(M_bdd, 0, thisParam);
                
                if (outerthis && binding.isConstructor()) {
                    addToFormal(M_bdd, 
                        binding.getParameterTypes().length + 1, 
                        StringWrapper.OUTER_THIS_FIELD);
                    if (useMrelations) {
                        addToMS(new MethodWrapper(bindings[i]), 
                            thisParam, StringWrapper.OUTER_THIS_FIELD, 
                            StringWrapper.OUTER_THIS_FIELD);
                    }
                    else addToS(thisParam, StringWrapper.OUTER_THIS_FIELD, StringWrapper.OUTER_THIS_FIELD);
                    
                    addToVT(StringWrapper.OUTER_THIS_FIELD, classBinding.getDeclaringClass());
                    
                }
                else if (generateVisited) {
                    String k = binding.getKey();
                    if (isInVisited(binding)) {
                        addToVisited(M_bdd);
                    }
                }
                
                M_bdd.free();
            }
        }

        public void endVisit(TypeDeclaration arg0) {
            declStack.pop();
            clinitStack.pop();
        }
        
        

        
        // Mret
        public boolean visit(ReturnStatement arg0) {
            return true;
        }   
        public void endVisit(ReturnStatement arg0) {
            Expression e = arg0.getExpression();
            if (e == null) return;
            ITypeBinding binding = e.resolveTypeBinding();
            if (binding.isPrimitive() || binding.isNullType()) return;
            
            MethodDeclaration m = (MethodDeclaration)findDeclaringParent();
            addMReturn(m, e);     
        }
        
        private void addMReturn(MethodDeclaration m, Expression e) {
            e = (Expression)stripParens(e);
            switch (e.getNodeType()) {
                case ASTNode.ASSIGNMENT:
                    addMReturn(m, ((Assignment)e).getLeftHandSide());
                    return;
                case ASTNode.CLASS_INSTANCE_CREATION:
                case ASTNode.ARRAY_CREATION:
                case ASTNode.STRING_LITERAL:
                case ASTNode.INFIX_EXPRESSION:
                case ASTNode.SIMPLE_NAME:
                case ASTNode.QUALIFIED_NAME:   
                case ASTNode.SUPER_FIELD_ACCESS:                       
                case ASTNode.FIELD_ACCESS:
                case ASTNode.CONDITIONAL_EXPRESSION:          
                case ASTNode.METHOD_INVOCATION:
                case ASTNode.SUPER_METHOD_INVOCATION: 
                case ASTNode.CAST_EXPRESSION:
                case ASTNode.ARRAY_ACCESS:
                    addToMret(m, new ASTNodeWrapper(e));
                    return;
                case ASTNode.THIS_EXPRESSION:
                    addToMret(m, new ThisWrapper(m, (ThisExpression)e));
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }
        }
        
        // Mthr
        public boolean visit(ThrowStatement arg0) {
            return true;
        }
        public void endVisit(ThrowStatement arg0) {
            ASTNode m = findThrowParent(arg0, 
                arg0.getExpression().resolveTypeBinding());
            
            if (m.getNodeType() == ASTNode.METHOD_DECLARATION) {
                addMThrow(new MethodWrapper((MethodDeclaration)m), 
                    arg0.getExpression());
            }
            else if (m.getNodeType() == ASTNode.INITIALIZER) {
                if (isStatic((Initializer)m)) {
                    addMThrow(getClinit(), arg0.getExpression());
                }
                else {
                    List l = getWrappedConstructors(findDeclaringParent());
                    for (Iterator i = l.iterator(); i.hasNext(); ) {
                        addMThrow((MethodWrapper)i.next(), arg0.getExpression());
                    }
                }
            }
        }
        private void addMThrow(Wrapper m, Expression e) {
            e = (Expression)stripParens(e);
            switch (e.getNodeType()) {
                case ASTNode.ASSIGNMENT:
                    addMThrow(m, ((Assignment)e).getLeftHandSide());
                    return;
                case ASTNode.CLASS_INSTANCE_CREATION:
                case ASTNode.ARRAY_CREATION:
                case ASTNode.STRING_LITERAL:
                case ASTNode.INFIX_EXPRESSION:
                case ASTNode.SIMPLE_NAME:
                case ASTNode.QUALIFIED_NAME:   
                case ASTNode.SUPER_FIELD_ACCESS:                       
                case ASTNode.FIELD_ACCESS:
                case ASTNode.CONDITIONAL_EXPRESSION:          
                case ASTNode.METHOD_INVOCATION:
                case ASTNode.SUPER_METHOD_INVOCATION: 
                case ASTNode.CAST_EXPRESSION:
                case ASTNode.ARRAY_ACCESS:
                    addToMthr(m, new ASTNodeWrapper(e));
                    return;
                case ASTNode.THIS_EXPRESSION:
                    addToMthr(m, new ThisWrapper(((MethodWrapper)m).getBinding(), 
                        (ThisExpression)e));
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }
        }
        
        /**
         * @param n Node from where to start searching for parent 
         *          (does not look at itself)
         * @param ex Exception being thrown.
         * @return returns the exception catch variable if exception is caught, 
         *          otherwise return method that throws it
         */
        private ASTNode findThrowParent(ASTNode n, ITypeBinding ex) {
            ASTNode prev;
            do {
                prev = n;
                n = n.getParent();
            } while (!(n.getNodeType() == ASTNode.METHOD_DECLARATION 
                    || n.getNodeType() == ASTNode.TRY_STATEMENT 
                    || n.getNodeType() == ASTNode.INITIALIZER
                    || n instanceof BodyDeclaration));
            
            if (n.getNodeType() == ASTNode.METHOD_DECLARATION 
                || n.getNodeType() == ASTNode.INITIALIZER 
                || n instanceof BodyDeclaration) return n;
            
            TryStatement t = (TryStatement)n;
            // n in finally?
            if (prev == t.getFinally()) return findThrowParent(t, ex); 
            
            Set stypes = getSuperTypes(ex);
            List catches = t.catchClauses();
            for (Iterator i = catches.iterator(); i.hasNext();) {
                Name var = ((CatchClause)i.next()).getException().getName();

                if (stypes.contains(var.resolveTypeBinding().getKey())) {
                    return var;// exception caught 
                }
            }
            
            return findThrowParent(t, ex); // exception uncaught
        }

        

        private List processStaticInit(Expression qualifier, 
            boolean methodStatic) {
            if (methodStatic) {
                return Collections.singletonList(StringWrapper.GLOBAL_THIS);
            }
            else { 
                ThisExpression t = null;
                if (qualifier != null && (t = getThis(qualifier)) == null) {
                    return Collections.singletonList(new ASTNodeWrapper(qualifier));
                }
                else { // implicit this or expr is thisexpr
                    throw new RuntimeException("ERROR: this pter in static initializer");
                   //return null;
                }
            }
        }
        
        private List processInitializer(Expression qualifier, 
            boolean methodStatic, List enclosingMethods, List ctors) {
            for (Iterator i = ctors.iterator(); i.hasNext(); ) {
                IMethodBinding mb = (IMethodBinding)i.next();
                enclosingMethods.add(new MethodWrapper(mb));
            }
            
            if (methodStatic) {
                return Collections.singletonList(StringWrapper.GLOBAL_THIS);   
            }
            else { 
                ThisExpression t = null;
                if (qualifier != null && (t = getThis(qualifier)) == null) {
                    return Collections.singletonList(new ASTNodeWrapper(qualifier));
                }
                else { // implicit this or expr is thisexpr
                    List thisParams = new ArrayList();
                    for (Iterator i = ctors.iterator(); i.hasNext(); ) {
                        thisParams.add(new ThisWrapper((IMethodBinding)i.next(), t));
                    }
                    return thisParams;
                }
            }
        }
        
        private List processEnclosedMethod(Expression qualifier, 
            boolean methodStatic, MethodDeclaration parent) {
            if (methodStatic) {
                return Collections.singletonList(StringWrapper.GLOBAL_THIS); 
            }
            else { 
                ThisExpression t = null;
                if (qualifier != null && (t = getThis(qualifier)) == null) {
                    return Collections.singletonList(new ASTNodeWrapper(qualifier));
                }
                else { // implicit this or expr is thisexpr
                    return Collections.singletonList(new ThisWrapper(parent, t)); 
                }
            }
        }
        
        // actual, Mthr, Iret, Ithr, IE0, mI
        public boolean visit(MethodInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveMethodBinding();
            //out.println(method.getName());
            boolean stat = isStatic(method);
            ASTNode decl = findDeclaringParent();
            List thisParams;
            List enclosingMethods;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION ||
                decl.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) { // in an initializer
                Initializer init = getInitializer(arg0);
                if (init == null) {
                    VariableDeclaration vd = getVarDecl(arg0);
                    if (isStatic(vd.getName())) {
                        enclosingMethods = Collections.singletonList(getClinit());
                        thisParams = processStaticInit(arg0.getExpression(), stat);
                    } 
                    else {
                        enclosingMethods = new ArrayList();
                        List ctors = getConstructors(decl);
                        thisParams = processInitializer(arg0.getExpression(), stat, 
                            enclosingMethods, ctors);
                    }
                }
                else if (isStatic(init)) {
                    enclosingMethods = Collections.singletonList(getClinit());
                    thisParams = processStaticInit(arg0.getExpression(), stat);
                }
                else {
                    enclosingMethods = new ArrayList();
                    List ctors = getConstructors(decl);
                    thisParams = processInitializer(arg0.getExpression(), stat, 
                        enclosingMethods, ctors);
                }
            }
            else {
                enclosingMethods = 
                    Collections.singletonList(new MethodWrapper((MethodDeclaration)decl));
                thisParams = processEnclosedMethod(arg0.getExpression(), 
                    stat, (MethodDeclaration)decl);               
            }
            
            Wrapper name;
            if (stat || isPrivate(method)) {
                name = new ASTNodeWrapper(null);
            }
            else {
                name = new MethodWrapper(method);
            }   

            List args = arg0.arguments();
            addMethodInvocation(thisParams, n, method, args, 
                enclosingMethods, name);
            
            return true; 
        }

        public boolean visit(SuperMethodInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveMethodBinding();
            
            boolean stat = isStatic(method);
            ASTNode decl = findDeclaringParent();
            List thisParams;
            List enclosingMethods;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION ||
                decl.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) { // in an initializer
                Initializer init = getInitializer(arg0);
                if (init == null) {
                    VariableDeclaration vd = getVarDecl(arg0);
                    if (isStatic(vd.getName())) {
                        enclosingMethods = Collections.singletonList(getClinit());
                        thisParams = processStaticInit(null, stat);
                    } 
                    else {
                        enclosingMethods = new ArrayList();
                        List ctors = getConstructors(decl);
                        thisParams = processInitializer(null, stat, 
                            enclosingMethods, ctors);
                    }
                }
                else if (isStatic(init)) {
                    enclosingMethods = Collections.singletonList(getClinit());
                    thisParams = processStaticInit(null, stat);
                }
                else {
                    enclosingMethods = new ArrayList();
                    List ctors = getConstructors(decl);
                    thisParams = processInitializer(null, stat, 
                        enclosingMethods, ctors);
                }
            }
            else {
                enclosingMethods = 
                    Collections.singletonList(new MethodWrapper((MethodDeclaration)decl));
                thisParams = processEnclosedMethod(null, 
                    stat, (MethodDeclaration)decl);               
            }
            // TODO if qualified, access outer class

            List args = arg0.arguments();
            addMethodInvocation(thisParams, n, method, 
                args, enclosingMethods, new ASTNodeWrapper(null));
            
            return true;
        }


        public boolean visit(ConstructorInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveConstructorBinding();   
            
            MethodDeclaration decl = 
                (MethodDeclaration)findDeclaringParent();
            List enclosingMethods = Collections.singletonList(new MethodWrapper(decl));
            List thisParams = Collections.singletonList(new ThisWrapper(decl, null));
                        
            List args = arg0.arguments();
            addMethodInvocation(thisParams, n, 
                method, args, enclosingMethods, new ASTNodeWrapper(null));
            return true; 
        }
        
        public boolean visit(SuperConstructorInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveConstructorBinding();
            
            MethodDeclaration decl = (MethodDeclaration)findDeclaringParent();
            List enclosingMethods = 
                Collections.singletonList(new MethodWrapper(decl));
            List thisParams = processEnclosedMethod(arg0.getExpression(), 
                false, decl);          
            
            List args = arg0.arguments();
            addMethodInvocation(thisParams, n, method, args, 
                enclosingMethods, new ASTNodeWrapper(null));
            
            return true; 
        }

        private void addMethodInvocation(List thisParams, 
                Wrapper invocation, IMethodBinding invocationBinding, 
                List args, List enclosingMethods, 
                Wrapper methodName) {
            int I_i = Imap.get(invocation);
            boolean nat = isNative(invocationBinding);
            //out.println("adding invocation #"+ I_i + " : "+ invocation);
            BDD I_bdd = I.ithVar(I_i);
            if (invocation instanceof ASTNodeWrapper) {
                ASTNode inv = ((ASTNodeWrapper)invocation).getNode();
                // Mthr, Ithr
                ITypeBinding[] exs = invocationBinding.getExceptionTypes();
                for (int i = 0; i < exs.length; i++) {
                    ExceptionWrapper ew = new ExceptionWrapper(inv, exs[i]);
                    addToIthr(I_bdd, ew); 
                    if (nat) {
                        if (useMrelations) addToMVP(enclosingMethods, ew, ew);
                        else addToVP(ew, ew);
                    }
                    
                    ASTNode parent = findThrowParent(inv, exs[i]);    
                    if (parent.getNodeType() == ASTNode.METHOD_DECLARATION) { 
                        addToMthr(new MethodWrapper((MethodDeclaration)parent), ew); // not caught
                    }  
                    else if (parent.getNodeType() == ASTNode.INITIALIZER 
                        || parent instanceof BodyDeclaration) { // not caught
                        for (Iterator j = enclosingMethods.iterator(); j.hasNext(); ) {
                            Wrapper w = (Wrapper)j.next();
                            addToMthr(w, ew);
                        }
                    }
                    else { // caught, match up with var
                        addToA(new ASTNodeWrapper(parent), ew);
                    }
                }
            }

            // actual
            for (Iterator i = thisParams.iterator(); i.hasNext(); ) {
                addToActual(I_bdd, 0, (Wrapper)i.next());
            }   

            Iterator it = args.iterator();
            for (int i = 1; it.hasNext(); i++) {
                Expression arg = (Expression)it.next();
                ITypeBinding argBinding = arg.resolveTypeBinding();
                if (argBinding.isPrimitive() || argBinding.isNullType()) continue;
                ThisExpression t = getThis(arg);
                if (t == null) {
                    addToActual(I_bdd, i, new ASTNodeWrapper(arg));
                }
                else {
                    for (Iterator j = enclosingMethods.iterator(); j.hasNext(); ) {
                        IMethodBinding mb = ((MethodWrapper)j.next()).getBinding();
                        addToActual(I_bdd, i, new ThisWrapper(mb, t));
                    }
                }
            }
            
            // Iret
            ITypeBinding retType = invocationBinding.getReturnType();
            if (!retType.isPrimitive()) {
                addToIret(I_bdd, invocation);
                if (nat) { // treat as new instantiation site
                    if (useMrelations) addToMVP(enclosingMethods, invocation, invocation);
                    else addToVP(invocation, invocation);
                }
                
            }
            
            // mI
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToMI((Wrapper)i.next(), I_bdd, methodName);
            }
            
            // IE
            if (!(methodName instanceof MethodWrapper)) {
                if (useMrelations) {
                    for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                        addToMIE((Wrapper)i.next(), I_bdd, invocationBinding);
                    }
                }
                else addToIE(I_bdd, invocationBinding); 
            }
            
            I_bdd.free();
            
            // link start() with run()
            if (invocationBinding.getName().equals("start") 
                && invocationBinding.getReturnType().getKey().equals("void") 
                && invocationBinding.getParameterTypes().length == 0) {// thread start()
                ITypeBinding declClass = invocationBinding.getDeclaringClass();
                IMethodBinding[] methods = declClass.getDeclaredMethods();
                IMethodBinding run = null;
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].getName().equals("run") 
                        && methods[i].getParameterTypes().length == 0 
                        && methods[i].getReturnType().getKey().equals("void")) {
                        run = methods[i];
                        break;
                    }   
                }
                if (run != null) {
                    StringWrapper runInv = 
                        new StringWrapper("DummyRun()Invocation derived from " 
                            + I_i + " : "+ invocation);
    
                    for (Iterator j = thisParams.iterator(); j.hasNext(); ) {     
                        addToActual(runInv, 0, (Wrapper)j.next());
                    }
                    
                    for (Iterator j = enclosingMethods.iterator(); j.hasNext(); ) {
                        addToMI((Wrapper)j.next(), 
                            runInv, new MethodWrapper(run));
                    }
                }
            }
            
        }
        
        public boolean visit(Initializer arg0) {
            initializers.add((TypeDeclaration)findDeclaringParent(), arg0);
            return true;
        }
        
        public void postVisit(ASTNode arg0) {
            //out.println(arg0);
        }
        public void preVisit(ASTNode arg0) {
            //out.println(arg0);
        }
        

        public boolean visit(SuperFieldAccess arg0) {
            // TODO Auto-generated method stub            // load
            System.err.println("ERROR: super field access unhandled");
            return false;// do not go into simplename
        }

        public boolean visit(LabeledStatement arg0) {
            arg0.getBody().accept(this);
            return false;
        }
        
        // empty visitors
        public boolean visit(Block arg0) {
            return true;
        }
        public boolean visit(VariableDeclarationExpression arg0) {
            return true;
        }
        public boolean visit(CatchClause arg0) {
            return true;
        }
        public boolean visit(TypeLiteral arg0) {
            return true;
        }
        public boolean visit(SimpleType arg0) {
            return true;
        }
        public boolean visit(TypeDeclarationStatement arg0) {
            return true;
        }
        public boolean visit(BooleanLiteral arg0) {
            return true;
        }
        public boolean visit(BreakStatement arg0) {
            return false;
        }
        public boolean visit(CharacterLiteral arg0) {
            return true;
        }
        public boolean visit(Modifier arg0) {
            return true;
        }
        public boolean visit(NullLiteral arg0) {
            return true;
        }
        public boolean visit(InstanceofExpression arg0) {
            return true;
        }
        public boolean visit(FieldDeclaration arg0) {
            return true; 
        }
        public boolean visit(VariableDeclarationStatement arg0) {
            return true;
        }
        public boolean visit(ThisExpression arg0) {
            return true;
        }
        public boolean visit(ArrayInitializer arg0) {
            return true;
        }
        public boolean visit(ArrayType arg0) {
            return true;
        }
        public boolean visit(AssertStatement arg0) {
            return true;
        }
        public boolean visit(ContinueStatement arg0) {
            return false; 
        }
        public boolean visit(DoStatement arg0) {
            return true; 
        }
        public boolean visit(ExpressionStatement arg0) {
            return true;
        }
        public boolean visit(ForStatement arg0) {
            return true;
        }
        public boolean visit(IfStatement arg0) {
            return true;
        }
        public boolean visit(ImportDeclaration arg0) {
            return true;
        }
        public boolean visit(NumberLiteral arg0) {
            return true;
        }
        public boolean visit(PackageDeclaration arg0) {
            return true;
        }
        public boolean visit(ParenthesizedExpression arg0) {
            return true;
        }
        public boolean visit(PostfixExpression arg0) {
            return true;
        }
        public boolean visit(PrefixExpression arg0) {
            return true;
        }
        public boolean visit(PrimitiveType arg0) {
            return true;
        }
        public boolean visit(SwitchCase arg0) {
            return true;
        }
        public boolean visit(SwitchStatement arg0) {
            return true;
        }
        public boolean visit(SynchronizedStatement arg0) {
            return true;
        }
        public boolean visit(TryStatement arg0) {
            return true;
        }
        public boolean visit(WhileStatement arg0) {
            return true;
        }     
        
        /* JLS3
        public boolean visit(EnhancedForStatement arg0) {
            return true; 
        }
        public boolean visit(EnumConstantDeclaration arg0) {
            return true; 
        }
        public boolean visit(EnumDeclaration arg0) {
            return true; 
        }              
        public boolean visit(AnnotationTypeDeclaration arg0) {
            return true;
        }
        public boolean visit(AnnotationTypeMemberDeclaration arg0) {
            return true;
        }
        public boolean visit(MarkerAnnotation arg0) {
            return true;
        }
        public boolean visit(MemberValuePair arg0) {
            return true;
        }        
        public boolean visit(NormalAnnotation arg0) {
            return true;
        }
        public boolean visit(ParameterizedType arg0) {
            return true;
        }        
        public boolean visit(QualifiedType arg0) {
            return true;
        }        
        public boolean visit(SingleMemberAnnotation arg0) {
            return true;
        }        
        public boolean visit(TypeParameter arg0) {
            return true;
        }        
        public boolean visit(WildcardType arg0) {
            return true;
        }
        */
        
        
        void addThisToA(ASTNode v1, ThisExpression e) {
            ASTNode n = findDeclaringParent();
            ASTNodeWrapper v = new ASTNodeWrapper(v1);
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                ITypeBinding p;
                if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
                    p = ((TypeDeclaration)n).resolveBinding();
                }
                else {
                    p = ((AnonymousClassDeclaration)n).resolveBinding();
                }
                IMethodBinding[] methods = p.getDeclaredMethods();
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].isConstructor()) {
                        addToA(v, new ThisWrapper(methods[i], e));
                    }
                }
            }
            else {
                addToA(v, new ThisWrapper((MethodDeclaration)n, e));  
            }
        }

        void addThisToA(ThisExpression e1, ThisExpression e2) {
            ASTNode n = findDeclaringParent();  
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                ITypeBinding p;
                if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
                    p = ((TypeDeclaration)n).resolveBinding();
                }
                else {
                    p = ((AnonymousClassDeclaration)n).resolveBinding();
                }
                IMethodBinding[] methods = p.getDeclaredMethods();
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].isConstructor()) {
                        addToA(new ThisWrapper(methods[i], e1), 
                            new ThisWrapper(methods[i], e2));
                    }
                }
            }
            else {
                MethodDeclaration decl = (MethodDeclaration)n;
                addToA(new ThisWrapper(decl, e1), new ThisWrapper(decl, e2));  
            }
        }
        
        void addThisToA(ThisExpression e, ASTNode v2) {
            ASTNode n = findDeclaringParent();
            ASTNodeWrapper v = new ASTNodeWrapper(v2);  
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                ITypeBinding p;
                if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
                    p = ((TypeDeclaration)n).resolveBinding();
                }
                else {
                    p = ((AnonymousClassDeclaration)n).resolveBinding();
                }
                IMethodBinding[] methods = p.getDeclaredMethods();
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].isConstructor()) {
                        addToA(new ThisWrapper(methods[i], e), v);
                    }
                }
            }
            else {
                addToA(new ThisWrapper((MethodDeclaration)n, e), v);  
            }
        }
        
        void addToA(ASTNode v1, ASTNode v2) {
            addToA(new ASTNodeWrapper(v1), new ASTNodeWrapper(v2));
        }
          
        void addToA(ASTNodeWrapper v1, ASTNodeWrapper v2) {  
            int V1_i = Vmap.get(v1);
            int V2_i = Vmap.get(v2);  
            BDD V_bdd = V1.ithVar(V1_i);        
            BDD bdd1 = V2.ithVar(V2_i);
            bdd1.andWith(V_bdd);// .id()?
            //out.println("adding to A " + v1 + " / " + v2); 
            if (TRACE_RELATIONS) out.println("Adding to A: "+bdd1.toStringWithDomains());
            A.orWith(bdd1);
        }
        
        void addToFormal(BDD M_bdd, int z, Wrapper v) {
            BDD bdd1 = Z.ithVar(z);
            int V_i = Vmap.get(v);
            bdd1.andWith(V1.ithVar(V_i));
            bdd1.andWith(M_bdd.id());
            out.println("adding to formal " + M_bdd.toStringWithDomains() + " / " + z + " / " + v); 
            if (TRACE_RELATIONS) out.println("Adding to formal: "+bdd1.toStringWithDomains());
            formal.orWith(bdd1);
        }
        
        
        void addToActual(BDD I_bdd, int z, Wrapper v) {
            BDD bdd1 = Z.ithVar(z);
            int V_i = Vmap.get(v);
            bdd1.andWith(V2.ithVar(V_i));
            bdd1.andWith(I_bdd.id());
            //out.println("adding to actual " + I_bdd.toStringWithDomains() + " / " + z + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to actual: "+bdd1.toStringWithDomains());
            actual.orWith(bdd1);
        }
        
        void addToActual(Wrapper inv, int z, Wrapper v) {
            int I_i = Imap.get(inv);
            BDD I_bdd = I.ithVar(I_i);
            addToActual(I_bdd, z, v);
            I_bdd.free();
        }


        void addToMS(Wrapper m, Wrapper v1,
            Wrapper f, Wrapper v2) {
            int M_i = Mmap.get(m);
            BDD M_bdd = M.ithVar(M_i);
            int V1_i = Vmap.get(v1);
            int V2_i = Vmap.get(v2);
            BDD V_bdd = V1.ithVar(V1_i);
            BDD bdd1 = V2.ithVar(V2_i);
            int F_i = Fmap.get(f);
            BDD F_bdd = F.ithVar(F_i);
            bdd1.andWith(F_bdd);
            bdd1.andWith(V_bdd);
            bdd1.andWith(M_bdd);
            //out.println("adding to S: " + v1 + " / " + f + " / "+ v2);
            if (TRACE_RELATIONS) out.println("Adding to mS: "+bdd1.toStringWithDomains());
            mS.orWith(bdd1);
        }


        void addToS(Wrapper v1, Wrapper f, Wrapper v2) {
            int V1_i = Vmap.get(v1);
            int V2_i = Vmap.get(v2);
            BDD V_bdd = V1.ithVar(V1_i);
            BDD bdd1 = V2.ithVar(V2_i);
            int F_i = Fmap.get(f);
            BDD F_bdd = F.ithVar(F_i);
            bdd1.andWith(F_bdd);
            bdd1.andWith(V_bdd);
            out.println("adding to S: " + v1 + " / " + f + " / "+ v2);
            if (TRACE_RELATIONS) out.println("Adding to S: "+bdd1.toStringWithDomains());
            S.orWith(bdd1);
        }
        
        
        void addToMS(Wrapper q, Wrapper f, Expression r) {
            ASTNode decl = findDeclaringParent(); 
            Wrapper nw;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION ||
                decl.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                Initializer init = getInitializer(r);
                if (init == null) {
                   VariableDeclaration vd = getVarDecl(r);
                   if (isStatic(vd.getName())) {
                       nw = getClinit();   
                   } 
                   else {
                       addToMS(getWrappedConstructors(decl), q, f, r);
                       return;
                   }
                }
                else if (isStatic(init)) {
                    nw = getClinit();  
                } 
                else {
                    addToMS(getWrappedConstructors(decl), q, f, r);
                    return;
                }
            }
            else {
                nw = new MethodWrapper((MethodDeclaration)decl);  
            }
            addToMS(nw, q, f, new ASTNodeWrapper(r));
        }

        void addToMS(Collection enclosingMethods, Wrapper q, 
            Wrapper f, Expression v2) {
            ASTNodeWrapper r = new ASTNodeWrapper(v2);
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToMS((Wrapper)i.next(), q, f, r);
            }
        }
        
        void addToS(ThisExpression e, SimpleName f, ASTNodeWrapper v2) {
            ASTNode n = findDeclaringParent();
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                ITypeBinding p;
                if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
                    p = ((TypeDeclaration)n).resolveBinding();
                }
                else {
                    p = ((AnonymousClassDeclaration)n).resolveBinding();
                }
                IMethodBinding[] methods = p.getDeclaredMethods();
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].isConstructor()) {
                        if (useMrelations) {
                            addToMS(new MethodWrapper(methods[i]), 
                                new ThisWrapper(methods[i], e), 
                                new FieldWrapper(f), v2);
                        }
                        else addToS(new ThisWrapper(methods[i], e), 
                            new FieldWrapper(f), v2);
                    }
                }
            }
            else {// method decl
                if (useMrelations) {
                    addToMS(new MethodWrapper((MethodDeclaration)n), 
                        new ThisWrapper((MethodDeclaration)n, e), 
                        new FieldWrapper(f), v2);
                }
                else addToS(new ThisWrapper((MethodDeclaration)n, e), 
                    new FieldWrapper(f), v2);
            }
        }
        
        void addToS(Wrapper v1, Wrapper f, 
            ThisExpression e) {
            ASTNode n = findDeclaringParent();
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                ITypeBinding p;
                if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
                    p = ((TypeDeclaration)n).resolveBinding();
                }
                else {
                    p = ((AnonymousClassDeclaration)n).resolveBinding();
                }
                IMethodBinding[] methods = p.getDeclaredMethods();
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].isConstructor()) {
                        if (useMrelations) {
                            addToMS(new MethodWrapper(methods[i]), v1, 
                                f, new ThisWrapper(methods[i], e));
                        }
                        else addToS(v1, f, new ThisWrapper(methods[i], e));
                    }
                }
            }
            else {// method decl
                if (useMrelations) {
                    addToMS(new MethodWrapper((MethodDeclaration)n), v1, 
                        f, new ThisWrapper((MethodDeclaration)n, e));
                }
                else addToS(v1, f, new ThisWrapper((MethodDeclaration)n, e));
            }
        }
        
        void addToS(ThisExpression e, SimpleName f, ThisExpression e2) {
            ASTNode n = findDeclaringParent();
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {        
                ITypeBinding p;
                if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
                    p = ((TypeDeclaration)n).resolveBinding();
                }
                else {
                    p = ((AnonymousClassDeclaration)n).resolveBinding();
                }
                IMethodBinding[] methods = p.getDeclaredMethods();
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].isConstructor()) {
                        if (useMrelations) {
                            addToMS(new MethodWrapper(methods[i]), 
                                new ThisWrapper(methods[i], e), 
                                new FieldWrapper(f), 
                                new ThisWrapper(methods[i], e2));
                        
                        }
                        else addToS(new ThisWrapper(methods[i], e), 
                            new FieldWrapper(f), 
                            new ThisWrapper(methods[i], e2));
                    }
                }
            }
            else {
                MethodDeclaration decl = (MethodDeclaration)n;
                if (useMrelations) {
                    addToMS(new MethodWrapper(decl), new ThisWrapper(decl, e), 
                        new FieldWrapper(f), 
                        new ThisWrapper(decl, e2));  
                }
                else addToS(new ThisWrapper(decl, e), new FieldWrapper(f), 
                        new ThisWrapper(decl, e2));  
            }
        }
        
        void addToL(Wrapper v1, Wrapper f, ASTNodeWrapper v2) {
            int V1_i = Vmap.get(v1);
            int V2_i = Vmap.get(v2);
            BDD V_bdd = V1.ithVar(V1_i);
            BDD bdd1 = V2.ithVar(V2_i);
            int F_i = Fmap.get(f);
            BDD F_bdd = F.ithVar(F_i);
            bdd1.andWith(F_bdd);
            bdd1.andWith(V_bdd);
            out.println("adding to L: " + v1 + " / " + f + " / "+ v2);
            if (TRACE_RELATIONS) out.println("Adding to L: "+bdd1.toStringWithDomains());
            L.orWith(bdd1);
        }
            
        void addToML(Wrapper m, Wrapper v1, 
            Wrapper f, ASTNodeWrapper v2) {

            int M_i = Mmap.get(m);
            BDD M_bdd = M.ithVar(M_i);
            int V1_i = Vmap.get(v1);
            int V2_i = Vmap.get(v2);
            BDD V_bdd = V1.ithVar(V1_i);
            BDD bdd1 = V2.ithVar(V2_i);
            int F_i = Fmap.get(f);
            BDD F_bdd = F.ithVar(F_i);
            bdd1.andWith(F_bdd);
            bdd1.andWith(V_bdd);
            bdd1.andWith(M_bdd);
            if (TRACE_RELATIONS) out.println("Adding to mL: "+bdd1.toStringWithDomains());
            mL.orWith(bdd1);
        }
        
        
        void addToML(Wrapper q, Wrapper f, Expression r) {
            ASTNode decl = findDeclaringParent(); 
            Wrapper nw;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION ||
                decl.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                Initializer init = getInitializer(r);
                if (init == null) {
                   VariableDeclaration vd = getVarDecl(r);
                   if (isStatic(vd.getName())) {
                       nw = getClinit();   
                   } 
                   else {
                       addToML(getWrappedConstructors(decl), q, f, r);
                       return;
                   }
                }
                else if (isStatic(init)) {
                    nw = getClinit();  
                } 
                else {
                    addToML(getWrappedConstructors(decl), q, f, r);
                    return;
                }
            }
            else {
                nw = new MethodWrapper((MethodDeclaration)decl);  
            }
            addToML(nw, q, f, new ASTNodeWrapper(r));
        }

        void addToML(Collection enclosingMethods, Wrapper q, 
            Wrapper f, Expression v2) {
            ASTNodeWrapper r = new ASTNodeWrapper(v2);
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToML((Wrapper)i.next(), q, f, r);
            }
        }
        
        void addToL(Wrapper v1, SimpleName f, ASTNode v2) {
            addToL(v1, new FieldWrapper(f), new ASTNodeWrapper(v2));        
        }
            
        void addToL(ThisExpression v1, SimpleName f, ASTNodeWrapper v2) {
            ASTNode n = findDeclaringParent();
            FieldWrapper fw = new FieldWrapper(f);

            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                ITypeBinding p;
                if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
                    p = ((TypeDeclaration)n).resolveBinding();
                }
                else {
                    p = ((AnonymousClassDeclaration)n).resolveBinding();
                }
                IMethodBinding[] methods = p.getDeclaredMethods();
                for (int i = 0; i < methods.length; i++) {
                    if (methods[i].isConstructor()) {
                        if (useMrelations) {
                            addToML(new MethodWrapper(methods[i]), 
                                new ThisWrapper(methods[i], v1), fw, v2); 
                        }
                        else addToL(new ThisWrapper(methods[i], v1), fw, v2);   
                    }
                }
            }
            else {// method decl
   
                if (useMrelations) {
                    addToML(new MethodWrapper((MethodDeclaration)n), 
                        new ThisWrapper((MethodDeclaration)n, v1), fw, v2);
                }
                else addToL(new ThisWrapper((MethodDeclaration)n, v1), fw, v2);
  
            }
        }
        
        void addToVP(Wrapper v, Wrapper h) {
            int i = Vmap.get(v);
            int V_i = i;
            int H_i = Hmap.get(h);
            BDD V_bdd = V1.ithVar(V_i);
            BDD bdd1 = H1.ithVar(H_i);
            bdd1.andWith(V_bdd); // .id()?
            out.println("adding to vP " + v + " / " + h); 
            if (TRACE_RELATIONS) out.println("Adding to vP: "+bdd1.toStringWithDomains());
            vP.orWith(bdd1);
        }
        
        void addToMVP(Wrapper m, Wrapper v, Wrapper h) {
            int M_i = Mmap.get(m);
            BDD M_bdd = M.ithVar(M_i);
            int V_i = Vmap.get(v);
            int H_i = Hmap.get(h);
            BDD V_bdd = V1.ithVar(V_i);
            BDD bdd1 = H1.ithVar(H_i);
            bdd1.andWith(V_bdd);
            bdd1.andWith(M_bdd);
            //out.println("adding to vP " + v + " / " + h); 
            if (TRACE_RELATIONS) out.println("Adding to vP: "+bdd1.toStringWithDomains());
            mvP.orWith(bdd1);
        }
        
        
        void addToMVP(ASTNodeWrapper v, ASTNodeWrapper h) {
            ASTNode decl = findDeclaringParent(); 
            Wrapper nw;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION ||
                decl.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                Initializer init = getInitializer(h.getNode());
                if (init == null) {
                   VariableDeclaration vd = getVarDecl(h.getNode());
                   if (isStatic(vd.getName())) {
                       nw = getClinit();   
                   } 
                   else {
                       addToMVP(getWrappedConstructors(decl), v, h);
                       return;
                   }
                }
                else if (isStatic(init)) {
                    nw = getClinit();  
                } 
                else {
                    addToMVP(getWrappedConstructors(decl), v, h);
                    return;
                }
            }
            else {
                nw = new MethodWrapper((MethodDeclaration)decl);  
            }
            addToMVP(nw, v, h);
        }
        
        StringWrapper getClinit() {
            return (StringWrapper)clinitStack.peek();
        }

    
        private VariableDeclaration getVarDecl(ASTNode node) {
            do {
                node = node.getParent();
            } while (!(node instanceof VariableDeclaration));
            return (VariableDeclaration)node;
        }

        void addToMVP(List enclosingMethods, Wrapper v, Wrapper h) {
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToMVP((Wrapper)i.next(), v, h);
            }
        }

        private void addToMret(MethodDeclaration m, ASTNodeWrapper v) {
            int V_i = Vmap.get(v);
            int M_i = Mmap.get(new MethodWrapper(m));
            BDD M_bdd = M.ithVar(M_i);
            BDD bdd1 = V2.ithVar(V_i);
            bdd1.andWith(M_bdd);
            //out.println("Adding to Mret: "+ new MethodWrapper(m) + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to Mret: "+bdd1.toStringWithDomains());
            Mret.orWith(bdd1);
            
        }
            
        private void addToMthr(Wrapper m, ASTNodeWrapper v) {
            int V_i = Vmap.get(v);
            int M_i = Mmap.get(m);
            BDD M_bdd = M.ithVar(M_i);
            BDD bdd1 = V2.ithVar(V_i);
            bdd1.andWith(M_bdd);
            //out.println("Adding to Mthr: "+ m + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to Mthr: "+bdd1.toStringWithDomains());
            Mthr.orWith(bdd1);        
        }
        

        void addToIret(BDD I_bdd, Wrapper v) {
            int V_i = Vmap.get(v);
            BDD bdd1 = V1.ithVar(V_i);
            bdd1.andWith(I_bdd.id());
            //out.println("Adding to Iret: "+ I_bdd.toStringWithDomains() + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to Iret: "+bdd1.toStringWithDomains());
            Iret.orWith(bdd1);
        }
        
        
        void addToIthr(BDD I_bdd, Wrapper v) {
            int V_i = Vmap.get(v);
            BDD bdd1 = V1.ithVar(V_i);
            bdd1.andWith(I_bdd.id());
            //out.println("Adding to Ithr: "+ I_bdd.toStringWithDomains() + " / " + v);       
            if (TRACE_RELATIONS) out.println("Adding to Ithr: "+bdd1.toStringWithDomains());
            Ithr.orWith(bdd1);
        }
        
        
        void addToMI(Wrapper m, StringWrapper inv, Wrapper target) {
            BDD I_bdd = I.ithVar(Imap.get(inv));
            addToMI(m, I_bdd, target);
            I_bdd.free();
        }
        
        

        void addToMI(Wrapper m, BDD I_bdd, Wrapper target) {
            BDD M_bdd = M.ithVar(Mmap.get(m));
            int N_i = Nmap.get(target);
            BDD bdd1 = N.ithVar(N_i);
            bdd1.andWith(M_bdd);
            bdd1.andWith(I_bdd.id());
            //out.println("Adding to mI: "+ m+ " / " +I_bdd.toStringWithDomains() + " / " + target); 
            if (TRACE_RELATIONS) out.println("Adding to mI: "+bdd1.toStringWithDomains());
            mI.orWith(bdd1);
        }
           
        void addToIE(BDD I_bdd, IMethodBinding target) {            
            int M2_i = Mmap.get(new MethodWrapper(target));
            BDD bdd1 = M.ithVar(M2_i);
            bdd1.andWith(I_bdd.id());
            //out.println("Adding to IE: "+ I_bdd.toStringWithDomains()+ 
            //    " / " +new MethodWrapper(target) ); 
            if (TRACE_RELATIONS) out.println("Adding to IE: "+bdd1.toStringWithDomains());
            IE.orWith(bdd1);
        }
        

        void addToMIE(Wrapper m, BDD I_bdd, IMethodBinding target) {
            int M_i = Mmap.get(m);
            BDD M_bdd = M.ithVar(M_i);
            int M2_i = Mmap.get(new MethodWrapper(target));
            BDD bdd1 = M2.ithVar(M2_i);
            bdd1.andWith(I_bdd.id());
            bdd1.andWith(M_bdd);
            if (TRACE_RELATIONS) out.println("Adding to mIE: "+bdd1.toStringWithDomains());
            mIE.orWith(bdd1);
        }
        
        void addToVisited(Wrapper m) {
            int M_i = Mmap.get(m);
            BDD M_bdd = M.ithVar(M_i);            
            if (TRACE_RELATIONS) out.println("Adding to visited: "+M_bdd.toStringWithDomains());
            visited.orWith(M_bdd);
        }
        
        void addToVisited(BDD M_bdd) {
            if (TRACE_RELATIONS) out.println("Adding to visited: "+M_bdd.toStringWithDomains());
            visited.orWith(M_bdd.id());
        }
        
        private ASTNode findDeclaringParent() {
            if (declStack.empty()) {
                throw new RuntimeException("ERROR empty decl stack");
                //return null;
            }
            
            return (ASTNode)declStack.peek();
            /*
            // walk up tree to find containing method
            while (!((n = n.getParent()) instanceof BodyDeclaration));
            
            if (n instanceof FieldDeclaration || n instanceof Initializer) {
                while (!((n = n.getParent()) instanceof TypeDeclaration));
                return (BodyDeclaration)n;
            }
            else if (n instanceof MethodDeclaration) return (BodyDeclaration)n;
            
            out.println("ERROR: unsupported parent of thisexpr");
            return null;
            */
        }
        
        
    }
    
    public static boolean isField(Name n) {
        IBinding bind = n.resolveBinding();
        if (bind.getKind() == IBinding.VARIABLE) {
            return ((IVariableBinding)bind).isField();
        }
        return false;
    }
    

    private Initializer getInitializer(ASTNode n) {
        do {
            n = n.getParent();
        } while (n.getNodeType() != ASTNode.INITIALIZER 
            && n.getNodeType() != ASTNode.TYPE_DECLARATION
            && n.getNodeType() != ASTNode.ANONYMOUS_CLASS_DECLARATION);
                    
        if (n.getNodeType() == ASTNode.TYPE_DECLARATION || 
            n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
            return null;
        }
        
        Initializer i = (Initializer)n;
        return i;
    }
    
    
    /**
     * Returns the ThisExpression that e contains
     * @param e
     * @return null if e doesn't unwrap to a ThisExpression
     */
    private ThisExpression getThis(Expression e) {
        e = (Expression)stripParens(e);
        
        if (e.getNodeType() == ASTNode.THIS_EXPRESSION) 
            return (ThisExpression)e;
        return null;
    }
    
    private static boolean isStatic(Name n) {
        return Modifier.isStatic(n.resolveBinding().getModifiers());
    }
    
    private static boolean isStatic(BodyDeclaration n) {
        return Modifier.isStatic(n.getModifiers());
    }
    
    private static boolean isStatic(IBinding b) {
        return Modifier.isStatic(b.getModifiers());
    }
    
    private static boolean isPrivate(IBinding b) {
        return Modifier.isPrivate(b.getModifiers());
    }
    
    private static boolean isNative(IBinding b) {
        return Modifier.isNative(b.getModifiers());
    }
    
    // Read in default properties.
    static { SystemProperties.read("pas.properties"); }
    
    static boolean USE_JOEQ_CLASSLIBS = !System.getProperty("pas.usejoeqclasslibs", "no").equals("no");

    Set dotJava;
    Set dotClass;
    Map/*<ICompilationUnit, CompilationUnit>*/ javaASTs = new HashMap();
    private boolean ran = false;
    String dumpPath;
    private int filesParsed = 0;
    private String loadPath;
    
    public PAFromSource(Set j, Set c) {
        this();
        parse(j, c);
    }
    
    public PAFromSource() {
        setPath();
        
        dotJava = new HashSet();
        dotClass = new HashSet();
        
        // TODO clear files?
        //resetBDDs();
        //initializeMaps();
    }

    private void setPath() {
        dumpPath = System.getProperty("pas.dumppath", "");
        loadPath = System.getProperty("pas.loadpath", "");
        String sep = System.getProperty("file.separator", "/");
        if (dumpPath.length() > 0) {
            File f = new File(dumpPath);
            if (!f.exists()) f.mkdirs();
            if (!dumpPath.endsWith(sep))
                dumpPath += sep;
        }
        if (loadPath.length() > 0) {
            File f = new File(loadPath);
            if (!loadPath.endsWith(sep))
                loadPath += sep;
        }
    }

    public SourceTransformation getTransformation() {
        if (ran) return new SourceTransformation(this);
        return null;
    }
    
    public static void main(String[] args) throws IOException {
        
        Set files;    
        if (args[0].startsWith("@")) {
            files = readClassesFromFile(args[0].substring(1));
        } else {
            files = new HashSet();
            files.add(args[0]);
        }
        
        PAFromSource dis = new PAFromSource(files, Collections.EMPTY_SET);
     
        dis.run();
    }

    
    private static Set readClassesFromFile(String fname) 
        throws IOException {
        
        BufferedReader r = null;
        try {
            r = new BufferedReader(new FileReader(fname));
            HashSet classes = new HashSet();
            String s = null;
            while ((s = r.readLine()) != null) {
                classes.add(s);
            }
            return classes;
        } finally {
            if (r != null) r.close();
        }
    }
    
    
    /**
     * @throws IOException
     */
    public void run() throws IOException {
        setPath();
        if (V1== null) return;
        if (filesParsed == 0) {
            out.println("nothing to generate relations for");
            return;
        }
        // Start timing.
        long time = System.currentTimeMillis();
        generateTypeRelations();
        System.out.println("Time spent : "+(System.currentTimeMillis()-time)/1000.);
        
        System.out.println("Writing relations...");
        time = System.currentTimeMillis();
        dumpBDDRelations();
        System.out.println("Time spent writing: "+(System.currentTimeMillis()-time)/1000.);

        out.println("Relations generated from " + filesParsed + " files.");
        
        out.println("Calling bddbddb to generate callgraph...");
        ran = true;
        // XXX ExternalAppLauncher.computeCallgraph(this);
       
        out.println("Calling bddbddb to genericize...");
        ExternalAppLauncher.genericize(this);   
        
    }

    private void generateTypeRelations() {
        // vT, aT
        out.println("adding to vT, aT, location2typevar ...");
        Iterator it = Vmap.iterator();
        for (int i = 0; it.hasNext(); i++) {
            Wrapper v =(Wrapper)it.next();
            // note: requires iterator to iterate in order of index
            // otherwise do i=Vmap.get(v) first
            addToVT(i, v); 
            addToAT(v);

            addToLocation2TypeVar(i, v);
        }
        out.println("TVmap size: " + TVmap.size());
        
        // hT;
        out.println("adding to hT ...");
        it = Hmap.iterator();
        for (int i = 0; it.hasNext(); i++) {
            Wrapper h =(Wrapper)it.next();
            addToHT(i, h);
        }

        // TODO transitive closure on aT
        
        out.println("adding to concreteTypes ...");
        it = Tmap.iterator();
        for (int i = 0; it.hasNext(); i++) {
            Wrapper t =(Wrapper)it.next();
            addToConcreteTypes(i, t);
        }
        out.println("TVmap size: " + TVmap.size());
        
        out.println("adding to field2typevar ...");
        it = Fmap.iterator();
        for (int i = 0; it.hasNext(); i++) {
            Wrapper f =(Wrapper)it.next();
            addToField2TypeVar(i, f);
        }
        out.println("TVmap size: " + TVmap.size());
        
        out.println("adding to ret2typevar ...");
        it = Mmap.iterator();
        for (int i = 0; it.hasNext(); i++) {
            Wrapper m =(Wrapper)it.next();
            addToRet2TypeVar(i, m);
        }
        out.println("TVmap size: " + TVmap.size());
        
        out.println("adding to param2typevar ...");
        for (it = formal.iterator(MZVset); it.hasNext(); ) {
            BDD b = (BDD)it.next();
            long[] l = b.scanAllVar();
            long m = l[M.getIndex()];
            long z = l[Z.getIndex()];
            Wrapper tv = (Wrapper)Vmap.get((int)l[V1.getIndex()]);
            addToParam2TypeVar(m, z, tv);
        }
        out.println("TVmap size: " + TVmap.size());
    }
    
    public void loadClasses(Set libs) {
        setPath();
        
        libs.removeAll(dotClass);
        System.out.println(libs.size() + " .class files to parse.");
        
        // make sure libs havn't been loaded first
        if (V1 == null) {
            if (!libs.isEmpty()) {
                Collection classes = new LinkedList();
                for (Iterator i = libs.iterator(); i.hasNext(); ) {
                    IClassFile f = (IClassFile) i.next();
                    String s = EclipseUtil.getFullyQualifiedClassName(f);
                    classes.add(s);
                }
                             
                ExternalAppLauncher.callJoeqGenRelations(classes, varorder);
                dotClass.addAll(libs);
            }
            
            loadFieldDomains();
            initBDDFactory();
            // load stuff back in
            resetBDDs();
            initializeMaps();
        }
        else {
            out.println("libs have already been loaded");
        }
    }

    public void parse(Set sources, Set libs) {
        setPath();
        // dont repeat work
        sources.removeAll(dotJava);
        libs.removeAll(dotClass);
        
        System.out.println(sources.size() + " .java files to parse.");
        System.out.println(libs.size() + " .class files to parse.");
        
        // make sure libs havn't been loaded first
        if (V1 == null) {
            initBDDFactory();
            // load stuff back in
            resetBDDs();
            initializeMaps();
        }
        
        
        // Start timing.
        long time = System.currentTimeMillis();
        
        int count = 1;
        out.println("Processing .java files");
        for (Iterator i = sources.iterator(); i.hasNext(); ) {
            ICompilationUnit o = (ICompilationUnit)i.next();
            out.println("Starting file " + count++);
            CompilationUnit cu = parseAST(o);
            if (cu != null) {
                javaASTs.put(o, cu);
                dotJava.add(o);
                generateRelations(cu, true, true);
            }
        }
        out.println(".java files processed");
    
        out.println("Processing .class files");
        for (Iterator i = libs.iterator(); i.hasNext(); ) {
            Object o = i.next();
            out.println("Starting file " + count++);
            CompilationUnit cu = parseAST(o);
            if (cu != null) {
                dotClass.add(o);
                generateRelations(cu, true, true);
            }
        }
        out.println(".class files processed");

        System.out.println("Time spent : "+(System.currentTimeMillis()-time)/1000.);
    }
    
    public void writeCallgraph(String file, MultiMap mm) throws IOException {
        BufferedWriter writer = new BufferedWriter(new FileWriter(file));
        
        for (Iterator it = classes.iterator(); it.hasNext(); ) {
            Object o = it.next();
            MethodDeclaration[] mds; 
            ITypeBinding t;
            if (o instanceof TypeDeclaration) {
                t = ((TypeDeclaration)o).resolveBinding();
                mds = ((TypeDeclaration)o).getMethods();
            }
            else {
                t = ((AnonymousClassDeclaration)o).resolveBinding();
                List l = ((AnonymousClassDeclaration)o).bodyDeclarations();
                ArrayList methods = new ArrayList();
                for (Iterator i = l.iterator(); i.hasNext(); ) {
                    Object obj = i.next();
                    if (obj instanceof MethodDeclaration) methods.add(obj);
                }
                mds = new MethodDeclaration[methods.size()];
                methods.toArray(mds);
            }

            // do static initializers
            ArrayList staticinits = new ArrayList();
            ArrayList notstatic = new ArrayList(); 
            partitionInitializers((ASTNode)o, staticinits, notstatic);
            
            writer.write("CLASS ");
            writer.write(t.getKey()); 
            writer.write('\n');
            
            if (!staticinits.isEmpty()) {
                writer.write(" METHOD <clinit> ()V ROOT\n");
                for (Iterator j = staticinits.iterator(); j.hasNext(); ) {
                    Initializer in = (Initializer)j.next();
                    in.accept(new CallGraphPrinter(writer, mm));
                }
            }
                        
            HashMap declaredMethods = new HashMap();

            for (int i = 0; i < mds.length; i++) {
                declaredMethods.put(mds[i].resolveBinding(), mds[i]);
            }

            IMethodBinding[] mb = getSortedMethods(t);

            for (int i = 0; i < mb.length; i++) {
                writeMethod(writer, mb[i]);
                if (mb[i].isConstructor()) {
                    for (Iterator j = notstatic.iterator(); j.hasNext(); ) {
                        Initializer in = (Initializer)j.next();
                        in.accept(new CallGraphPrinter(writer, mm));
                    }

                    // implicit calls to superconstructor?
                    String s = IMPLICITSUPERCALL + mb[i].getKey();
                    Collection targets = mm.getValues(s);
                    if (!targets.isEmpty()) {
                        writeCallsite(writer, targets, new StringWrapper(s));
                    }
                }

                MethodDeclaration md = (MethodDeclaration)declaredMethods.get(mb[i]);
                if (md != null) {
                    md.accept(new CallGraphPrinter(writer, mm));
                }
                
            }
        }
        
        writer.close();
    }

    
    private IMethodBinding[] getSortedMethods(ITypeBinding t) {
        IMethodBinding[] mb = t.getDeclaredMethods();
        Arrays.sort(mb, new Comparator() {
            public int compare(Object o1, Object o2) {
                String s1 = getFormattedName((IMethodBinding)o1);
                String s2 = getFormattedName((IMethodBinding)o2);
                return s1.compareTo(s2);
            }});
        return mb;
    }

    private void partitionInitializers(ASTNode td, ArrayList staticinits, ArrayList notstatic) {
        if (td.getNodeType() == ASTNode.TYPE_DECLARATION) {
            Collection inits = initializers.getValues(td);
            for (Iterator j = inits.iterator(); j.hasNext(); ) {
                Initializer in = (Initializer)j.next();
                
                if (isStatic(in)) staticinits.add(in);
                else notstatic.add(in);
            }
        }
        else {
            List l = ((AnonymousClassDeclaration)td).bodyDeclarations();
            for (Iterator i = l.iterator(); i.hasNext(); ) {
                Object obj = i.next();
                if (obj instanceof Initializer) {
                    Initializer in = (Initializer)obj;
                    
                    if (isStatic(in)) staticinits.add(in);
                    else notstatic.add(in);
                }
            }
        }
    }

    private void writeCallsite(BufferedWriter writer, Collection targets, 
        Wrapper w) throws IOException {
        writer.write("  CALLSITE ");
        writer.write(String.valueOf(Imap.get(w)));
        writer.write('\n');
        
        for (Iterator j = targets.iterator(); j.hasNext(); ) { 
            Object m = j.next();
            writeTarget(writer, (Wrapper)m);
        }
    }
    
    
    private boolean isInVisited(IMethodBinding binding) {
        String name = binding.getName();
        //out.println(name);
        if (binding.getReturnType().getKey().equals("void")) {
            ITypeBinding[] params = binding.getParameterTypes();
            if (params.length == 0) {
                if (name.equals("finalize") || name.equals("run")) return true;
            }
            else if (params.length == 1 && isStatic(binding)) {
                //out.println(params[0].getKey());
                if (params[0].getKey().equals("java/lang/String1") 
                    && name.equals("main")) return true;
            }
        }
        return false;
    }


    private void writeTarget(BufferedWriter writer, Wrapper mw) throws IOException {
        writer.write("   TARGET ");
        if (mw instanceof MethodWrapper) {
            IMethodBinding binding = ((MethodWrapper)mw).getBinding();
            writer.write(binding.getDeclaringClass().getKey());
            writer.write('.');
            writer.write(getFormattedName(binding));
        }
        else {
            writer.write(mw.toString());
            writer.write(" from StringWrapper");
        }
        writer.write('\n');
    }

    
    private void writeMethod(BufferedWriter writer, IMethodBinding mb) throws IOException {
        writer.write(" METHOD ");
        writer.write(getFormattedName(mb));
        if (isInVisited(mb)) {
            writer.write(" ROOT");
        }
        writer.write("\n");
    }
    
    private String getFormattedName(IMethodBinding mb) {
        StringBuffer sb = new StringBuffer(mb.isConstructor()? "<init>": mb.getName());
        sb.append(" (");
        ITypeBinding[] tb = mb.getParameterTypes();
        for (int i = 0; i < tb.length; i++) {
            sb.append(getFormattedType(tb[i]));
        }
        sb.append(')');
        sb.append(getFormattedType(mb.getReturnType()));
        return sb.toString();
    }
    
    private String getFormattedType(ITypeBinding t) {
        if (t.isArray()) {
            int dim = t.getDimensions();
            StringBuffer brackets = new StringBuffer('[');
            while (dim > 1) {
                brackets.append('[');
                dim --;
            }
            return brackets.append(getFormattedType(t.getElementType())).toString();
        }
        else {
            if (t.isPrimitive()) return t.getBinaryName();
            return "L" + t.getKey() + ';';
        }
    }
    
    
    public MultiMap parseIETuples(String file) throws IOException {
        BufferedReader in = new BufferedReader(new FileReader(file));
        MultiMap mm = new GenericMultiMap();
        String line;
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                
            String[] tuple = line.split("\\s"); // (I, M)
            
            Object i;
            Wrapper wrapper = (Wrapper)Imap.get(Integer.parseInt(tuple[0]));
            if (wrapper instanceof StringWrapper) {
                i = ((StringWrapper)wrapper).getString();
            }
            else {
                i = ((ASTNodeWrapper)wrapper).getNode();
            }
            Object m = Mmap.get(Integer.parseInt(tuple[1]));
            
            mm.add(i, m);
        }
        
        in.close();
        return mm;
    }

    class CallGraphPrinter extends ASTVisitor {

        BufferedWriter writer;
        MultiMap ie;

        CallGraphPrinter(BufferedWriter w, MultiMap mm) { 
            super(false); 
            writer = w; 
            ie = mm;
        }
        
        public void postVisit(ASTNode arg0) {
        }
        public void preVisit(ASTNode arg0) {
        }
        
        // don't traverse inner types. will be taken care of by other printers
        public boolean visit(AnonymousClassDeclaration node) {
            return false;
        }
        public boolean visit(TypeDeclaration node) {
            return false;
        }
        
        public void endVisit(SuperMethodInvocation arg0) { 
            print(arg0);
        }
        public void endVisit(MethodInvocation arg0) {
            print(arg0);
        }
        public void endVisit(SuperConstructorInvocation arg0) {
            print(arg0);
        }
        public void endVisit(ClassInstanceCreation arg0) {
            print(arg0);
        }
        public void endVisit(ConstructorInvocation arg0) {
            print(arg0);
        }
        
        private void print(ASTNode n) {
            try {
                writeCallsite(writer, ie.getValues(n), new ASTNodeWrapper(n));
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
  
    private void dumpBDDRelations() throws IOException {     
        new ClassHierarchyAnalysis(this).calculateCHA();
        
        // difference in compatibility
        BDD S0 = S;//.exist(V1cV2cset);
        BDD L0 = L;//.exist(V1cV2cset);
        BDD IE0 = IE;//.exist(V1cV2cset);
        BDD vP0 = vP;//vP.exist(V1cH1cset);

        System.out.println("Dumping to path "+dumpPath);
        
        BufferedWriter dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"bddinfo"));
            for (int i = 0; i < bdd.numberOfDomains(); ++i) {
                BDDDomain d = bdd.getDomain(i);
                if (d == V1 || d == V2)
                    dos.write("V\n");
                else if (d == H1|| d == H2)
                    dos.write("H\n");
                else if (d == T1 || d == T2)
                    dos.write("T\n");
                else if (d == F)
                    dos.write("F\n");
                else if (d == I)
                    dos.write("I\n");
                else if (d == Z)
                    dos.write("Z\n");
                else if (d == N)
                    dos.write("N\n");
                else if (d == M || d == M2)
                    dos.write("M\n");
                else if (d == TV)
                    dos.write("TV\n");
                /*else if (Arrays.asList(V1c).contains(d)
                        || Arrays.asList(V2c).contains(d))
                    dos.write("VC\n");
                else if (Arrays.asList(H1c).contains(d)
                        || Arrays.asList(H2c).contains(d))
                    dos.write("HC\n");
                else if (DUMP_SSA) {
                    dos.write(bddIRBuilder.getDomainName(d)+"\n");
                }*/
                else
                    dos.write(d.toString() + "\n");
            }
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"fielddomains.pa"));
            dos.write("V "+(1L<<V_BITS)+" var.map\n");
            dos.write("H "+(1L<<H_BITS)+" heap.map\n");
            dos.write("T "+(1L<<T_BITS)+" type.map\n");
            dos.write("F "+(1L<<F_BITS)+" field.map\n");
            dos.write("I "+(1L<<I_BITS)+" invoke.map\n");
            dos.write("Z "+(1L<<Z_BITS)+"\n");
            dos.write("N "+(1L<<N_BITS)+" name.map\n");
            dos.write("M "+(1L<<M_BITS)+" method.map\n");
            dos.write("TV "+(1L<<TV_BITS)+" typevar.map\n");
            //dos.write("VC "+(1L<<VC_BITS)+"\n");
            //dos.write("HC "+(1L<<HC_BITS)+"\n");
            //if (bddIRBuilder != null) bddIRBuilder.dumpFieldDomains(dos);
        } finally {
            if (dos != null) dos.close();
        }
        /*
        BDD mC = bdd.zero();
        for (Iterator i = visited.iterator(Mset); i.hasNext(); ) {
            BDD m = (BDD) i.next();
            int m_i = (int) m.scanVar(M);
            jq_Method method = (jq_Method) Mmap.get(m_i);
            BDD c = getV1V2Context(method);
            if (c != null) {
                BDD d = c.exist(V2cset); c.free();
                m.andWith(d);
            }
            mC.orWith(m);
        }
        */
        bdd.save(dumpPath+"vP0.bdd", vP0);
        //bdd.save(dumpPath+"hP0.bdd", hP);
        bdd.save(dumpPath+"L.bdd", L0);
        bdd.save(dumpPath+"S.bdd", S0);
        /*if (CONTEXT_SENSITIVE) {
            bdd.save(dumpPath+"cA.bdd", A);
        } else */{
            bdd.save(dumpPath+"A.bdd", A);
        }
        bdd.save(dumpPath+"vT.bdd", vT);
        bdd.save(dumpPath+"hT.bdd", hT);
        bdd.save(dumpPath+"aT.bdd", aT);
        bdd.save(dumpPath+"cha.bdd", cha);
        bdd.save(dumpPath+"actual.bdd", actual);
        bdd.save(dumpPath+"formal.bdd", formal);
        //bdd.save(dumpPath+"mV.bdd", mV);
        //bdd.save(dumpPath+"mC.bdd", mC);
        bdd.save(dumpPath+"mI.bdd", mI);
        bdd.save(dumpPath+"Mret.bdd", Mret);
        bdd.save(dumpPath+"Mthr.bdd", Mthr);
        bdd.save(dumpPath+"Iret.bdd", Iret);
        bdd.save(dumpPath+"Ithr.bdd", Ithr);
        bdd.save(dumpPath+"IE0.bdd", IE0);
        bdd.save(dumpPath+"visited.bdd", visited);
        bdd.save(dumpPath+"mIE.bdd", mIE);
        bdd.save(dumpPath+"mS.bdd", mS);
        bdd.save(dumpPath+"mL.bdd", mL);
        bdd.save(dumpPath+"mvP.bdd", mvP);
        bdd.save(dumpPath+"location2typevar.bdd", location2typevar);
        bdd.save(dumpPath+"param2typevar.bdd", param2typevar);
        bdd.save(dumpPath+"field2typevar.bdd", field2typevar);        
        bdd.save(dumpPath+"ret2typevar.bdd", ret2typevar);  
        bdd.save(dumpPath+"concreteTypes.bdd", concreteTypes);  
                
        //bdd.save(dumpPath+"sync.bdd", sync);
        /*if (threadRuns != null)
            bdd.save(dumpPath+"threadRuns.bdd", threadRuns);
        if (IEfilter != null)
            bdd.save(dumpPath+"IEfilter.bdd", IEfilter);
        bdd.save(dumpPath+"roots.bdd", getRoots());

        if (V1c.length > 0 && H1c.length > 0) {
            bdd.save(dumpPath+"eq.bdd", V1c[0].buildEquals(H1c[0]));
        }
        */
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"var.map"));
            Vmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"heap.map"));
            Hmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"type.map"));
            Tmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"field.map"));
            Fmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"invoke.map"));
            Imap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"name.map"));
            Nmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"method.map"));
            Mmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(dumpPath+"typevar.map"));
            TVmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
    }
    
    private IndexedMap makeMap(String name, int bits) {
        BufferedReader in = null;
        try {
            in = new BufferedReader(new FileReader(loadPath+name+".map"));
            out.println("loading existing map " + name);
            IndexedMap m = NodeWrapperIndexMap.loadStringWrapperMap(name, in); 
            out.println("size: " + m.size());
            return m;
        } catch (IOException x) {
        }
        return new NodeWrapperIndexMap(name, 1 << bits);
    }

    private void initializeMaps() {
        out.println("loadpath " + loadPath);
        Vmap = makeMap("var", V_BITS);
        Imap = makeMap("invoke", I_BITS);
        Hmap = makeMap("heap", H_BITS);
        Fmap = makeMap("field", F_BITS);
        Tmap = makeMap("type", T_BITS);
        Nmap = makeMap("name", N_BITS);
        Mmap = makeMap("method", M_BITS);
        TVmap = makeMap("typevar", TV_BITS);
        out.println("maps loaded");
        
        Vmap.get(StringWrapper.GLOBAL_THIS);
        Hmap.get(StringWrapper.GLOBAL_THIS);
        Tmap.get(StringWrapper.GLOBAL_THIS);
        Mmap.get(StringWrapper.DUMMY_METHOD); 
    }

    private void generateASTs(Set files) {
        long time = System.currentTimeMillis();
        int k = 1;
        for (Iterator i = files.iterator(); i.hasNext(); k++) {
            Object o = i.next();
            if (k % 10 == 0) System.gc();
            parseAST(o);
        }
    
        System.out.println("Time spent parsing: "+(System.currentTimeMillis()-time)/1000.);
    }
    
    
    private CompilationUnit parseAST(Object file) {
        CompilationUnit cu;
        try {
            if (file instanceof String) {
                cu = readSourceFile((String) file);
            } else {
                ASTParser c = ASTParser.newParser(AST.JLS3);
                if (file instanceof ICompilationUnit)
                    c.setSource((ICompilationUnit) file);
                else
                    c.setSource((IClassFile) file);
                c.setResolveBindings(true);
                
                cu = (CompilationUnit) c.createAST(null);
            }
            
            boolean problems = false; 
            IProblem[] probs = cu.getProblems();
            for (int j = 0; j < probs.length; j++) {
                if (probs[j].isError()) {
                    problems = true;
                    System.out.println(probs[j].getMessage());
                }
            }
            
            if (problems) {
                System.out.println("Parse error... skipping.");
            }
            else {
                System.out.println("Parse success.");
                return cu;
            }                
        }
        catch (IllegalStateException e) {
            if (file instanceof IClassFile) {// no source attachment?
                out.println("Parse error... IllegalStateException: " + e.getMessage());
            }
            else {// otherwise ignore
                e.printStackTrace();
            }
        }
        return null;
    }

    private void generateRelations(CompilationUnit cu, 
        boolean libs, boolean root) {
        ++filesParsed;
        
        //cu.accept(new ConstructorVisitor());
        cu.accept(new PAASTVisitor(libs, root));  

    }
    
    private static CompilationUnit readSourceFile(String fname) {        
        System.out.print("parsing file: " + fname);
 
        StringBuffer sb = new StringBuffer();
        try {
            BufferedReader br = new BufferedReader(new FileReader(fname));
            int c;
            while ((c = br.read()) != -1) {
                sb.append((char) c);
            }
            br.close();
        }
        catch (IOException e) {
            System.out.println(" ... error opening file. Exiting.");
            System.exit(1);
        }
        
        char[] source = new char[sb.length()];
        sb.getChars(0, sb.length(), source, 0);
        
        ASTParser parser = ASTParser.newParser(AST.JLS3); 
        parser.setResolveBindings(true);
        parser.setUnitName(fname);
        parser.setSource(source); 
        CompilationUnit cu = (CompilationUnit)parser.createAST(null);
        if (cu.getMessages().length == 0) {
            System.out.println(" ... complete."); 
        }
        else {
            System.out.println(" ... parse error. Exiting.");
            System.exit(1);
        }
        
        return cu;
    }

    private void addToVT(StringWrapper v, ITypeBinding type) {
        int V_i = Vmap.get(v);
        BDD bdd1 = V1.ithVar(V_i);
        TypeWrapper tw = new TypeWrapper(type);
        int T_i = Tmap.get(tw);
        bdd1.andWith(T1.ithVar(T_i));
        out.println("adding to vT: " + V_i + " " + v+  " / " +
            tw.getTypeName());
        if (TRACE_RELATIONS) out.println("Adding to vT: "+bdd1.toStringWithDomains());
        vT.orWith(bdd1);
    }
      
    private void addToLocation2TypeVar(int V_i, Wrapper v) {
        if (v.equals(StringWrapper.GLOBAL_THIS)) return;
        BDD bdd1 = V1.ithVar(V_i);
        bdd1.andWith(TV.ithVar(TVmap.get(v)));
        if (TRACE_RELATIONS) out.println("Adding to location2typevar: "+bdd1.toStringWithDomains());
        location2typevar.orWith(bdd1);
        
    }
    
    private void addToConcreteTypes(int T_i, Wrapper t) {
        if (t.equals(StringWrapper.GLOBAL_THIS)) return;
        if (t.equals(new StringWrapper("null"))) return;
        BDD bdd1 = T1.ithVar(T_i);
        bdd1.andWith(TV.ithVar(TVmap.get(t)));
        if (TRACE_RELATIONS) out.println("Adding to concreteTypes: "+bdd1.toStringWithDomains());
        concreteTypes.orWith(bdd1);
    }
    
    private void addToField2TypeVar(int F_i, Wrapper f) {
        if (f.equals(new StringWrapper("null"))) return;       
        BDD bdd1 = F.ithVar(F_i);
        bdd1.andWith(TV.ithVar(TVmap.get(f)));
        if (TRACE_RELATIONS) out.println("Adding to field2typevar: "+bdd1.toStringWithDomains());
        field2typevar.orWith(bdd1);
    }
    
    private void addToRet2TypeVar(int M_i, Wrapper m) {
        if (m.equals(StringWrapper.DUMMY_METHOD)) return;    
        if (m instanceof StringWrapper) { // remove primitive returns
            String s = ((StringWrapper)m).getString();
            if (s.endsWith(".<clinit>")) return;

            // might catch more methods than desired if 
            // method is contained in another method
            if (s.lastIndexOf("/void") != -1) return;
            if (s.lastIndexOf("/int") != -1) return; 
            if (s.lastIndexOf("/long") != -1) return; 
            if (s.lastIndexOf("/char") != -1) return;
            if (s.lastIndexOf("/byte") != -1) return; 
            if (s.lastIndexOf("/boolean") != -1) return;
            if (s.lastIndexOf("/short") != -1) return;
            if (s.lastIndexOf("/float") != -1) return;
            if (s.lastIndexOf("/double") != -1) return;
        }
        else if (((MethodWrapper)m).getReturnType().isPrimitive()) return;
            
        BDD bdd1 = M.ithVar(M_i);
        bdd1.andWith(TV.ithVar(TVmap.get(m)));
        if (TRACE_RELATIONS) out.println("Adding to ret2typevar: "+bdd1.toStringWithDomains());
        ret2typevar.orWith(bdd1);
    }
    
    private void addToParam2TypeVar(long M_i, long z, Wrapper tv) {
        if (tv.equals(StringWrapper.GLOBAL_THIS)) return;
        BDD bdd1 = M.ithVar(M_i);
        bdd1.andWith(Z.ithVar(z));
        bdd1.andWith(TV.ithVar(TVmap.get(tv)));
        if (TRACE_RELATIONS) out.println("Adding to param2typevar: "+bdd1.toStringWithDomains());
        param2typevar.orWith(bdd1);
    }
    
    private void addToVT(int V_i, Wrapper v) {
        if (v instanceof TypeWrapper || v instanceof MethodWrapper) {
            throw new RuntimeException("ERROR: this type of node shouldn't be in V: " + v);
            //return;
        }
        
        ITypeBinding type = v.getType();
        if (type == null) {
            if (v instanceof StringWrapper) {
                if (v.equals(StringWrapper.GLOBAL_THIS)) {
                    BDD bdd1 = V1.ithVar(V_i);
                    bdd1.andWith(T1.ithVar(0));
                    //out.println("adding to vT: 0 / " + StringWrapper.GLOBAL_THIS);
                    if (TRACE_RELATIONS) out.println("Adding to vT: "+bdd1.toStringWithDomains());
                    vT.orWith(bdd1);
                }
                else if (v.equals(StringWrapper.OUTER_THIS_FIELD)) {
                    // vT added added when OUTER_THIS_FIELD is added to Vmap
                    return;
                }
                else {
                    // Maybe from Joeq, so we don't know about it.
                    //throw new RuntimeException("ERROR: unhandled stringwrapper node in V: " + v);
                }
            }
            else throw new RuntimeException("ERROR: gettype returned null");
        }
        else {
            BDD bdd1 = V1.ithVar(V_i);
            TypeWrapper tw = new TypeWrapper(type);
            int T_i = Tmap.get(tw);
            bdd1.andWith(T1.ithVar(T_i));
            //out.println("adding to vT: " + V_i + " " + v+  " / " +
                //tw.getTypeName());
            if (TRACE_RELATIONS) out.println("Adding to vT: "+bdd1.toStringWithDomains());
            vT.orWith(bdd1);
        }
    }
    
    private void addToHT(int H_i, Wrapper h) {
        if (h.equals(StringWrapper.GLOBAL_THIS)) return;
        if (h instanceof StringWrapper) {
            // From Joeq.
            return;
        }
        if (h instanceof ThisWrapper || h instanceof MethodWrapper ||
            h instanceof TypeWrapper) {
            throw new RuntimeException("ERROR: this type of node shouldn't be in H");
        }
        else {
            ITypeBinding type = h.getType();
            if (type == null) {
                throw new RuntimeException("ERROR: this type of node shouldn't be in H");
            }
            TypeWrapper tw = new TypeWrapper(type);
            int T_i = Tmap.get(tw);
            BDD T_bdd = T2.ithVar(T_i);
            BDD bdd1 = H1.ithVar(H_i);
            bdd1.andWith(T_bdd);
            //out.println("adding to hT: " + H_i + " " + h+ 
              //  " / " + tw.getTypeName());
            if (TRACE_RELATIONS) out.println("Adding to hT: "+bdd1.toStringWithDomains());
            hT.orWith(bdd1);
        }        
    }
    
    // supertype, subtype
    private void addToAT(Wrapper t1, Wrapper t2) {
        int T1_i = Tmap.get(t1);
        int T2_i = Tmap.get(t2);
        BDD T1_bdd = T1.ithVar(T1_i);
        BDD bdd1 = T2.ithVar(T2_i);
        bdd1.andWith(T1_bdd);
       // out.println("Adding to aT: "+ T1_i + " " + t1+" / " + T2_i + " " + t2);
        if (TRACE_RELATIONS) out.println("Adding to aT: "+bdd1.toStringWithDomains());
        aT.orWith(bdd1);
    }
    
    private List addBindingToAT(ITypeBinding binding) {
        List types = new LinkedList();
        if (binding.isPrimitive()) return types;
        TypeWrapper tw = new TypeWrapper(binding);
        types.add(tw.getTypeName());
        addToAT(tw, tw);// reflexive?
        ITypeBinding superBinding = binding.getSuperclass();
        if (superBinding != null) {
            //out.println(binding+", Super: " + superBinding);
            TypeWrapper stw = new TypeWrapper(superBinding);
            addToAT(stw, tw);
            types.add(stw.getTypeName());
        }
        ITypeBinding[] interfaces = binding.getInterfaces();
        for (int i = 0; i < interfaces.length; i++) {
            TypeWrapper stw = new TypeWrapper(interfaces[i]);
            addToAT(stw, tw);
            types.add(stw.getTypeName());
        }
        return types;
    }


    
    private String getArrayBrackets(int dim) {
        StringBuffer brackets = new StringBuffer("[]");
        while (dim > 1) {
            brackets.append("[]");
            dim --;
        }
        return brackets.toString();
    }


    private void addToAT(Wrapper w) {
        //Expression e = (Expression) w.getNode();
        //if (e == null) return;
        ITypeBinding t = w.getType();//.resolveTypeBinding();
        if (t == null) return;
        if (t.isArray()) addArrayToAT(t);
        else addBindingToAT(t);
    }

    private void addArrayToAT(ITypeBinding array) {
        // add itself
        TypeWrapper t = new TypeWrapper(array);
        addToAT(t, t);
        
        // add implemented interfaces
        addToAT(CLONEABLE, t);
        addToAT(SERIALIZABLE, t);
        addToAT(OBJECT, t);
        
        ITypeBinding elemType = array.getElementType();
        List basetypes = addBindingToAT(array.getElementType());

        int dim = array.getDimensions();
        
        // add [] to returned superclasses of stripped array
        if (dim > 1) {
            // strip []
            String name = t.getTypeName();
            List types2 = addArrayToAT(name.substring(0, name.length() - 2), 
                                        basetypes, dim - 1);
            for (Iterator i = types2.iterator(); i.hasNext(); ) {
                String s = (String)i.next();
                s += "[]";
                addToAT(new StringWrapper(s), t);
            }
        }
        
        String brackets = getArrayBrackets(dim);       
        for (Iterator i = basetypes.iterator(); i.hasNext(); ) {
            String s = (String)i.next();
            s += brackets;
            addToAT(new StringWrapper(s), t);
        }
    }
    
    /**
     * This is used only for multidim arrays, and is called only by 
     * the version that takes bindings.
     * Necessary since I can't obtain bindings for C[] from bindings of C[][].
     * @param array Qualified name of array type.
     * @param basetypes List of bindings for supertypes of C in C[]...[].
     * @param dim Number of [] in array.
     * @return List of qualified names of supertypes of array.
     */
    private List addArrayToAT(String array, List basetypes, int dim) {
        if (dim == 0) return null; // base case
        
        List/*String*/ types = new LinkedList();
        
        // add itself
        StringWrapper t = new StringWrapper(array);
        addToAT(t, t);
        types.add(array);
        
        // add implemented interfaces
        addToAT(CLONEABLE, t);
        addToAT(SERIALIZABLE, t);
        addToAT(OBJECT, t);
        types.add(CLONEABLE.getTypeName());
        types.add(SERIALIZABLE.getTypeName());
        types.add(OBJECT.getTypeName());   
        
        // add [] to returned superclasses of stripped array
        if (dim > 1) {
            // strip [] and add to types
            List types2 = addArrayToAT(array.substring(0, array.length() - 2), 
                                        basetypes, dim - 1);
            for (Iterator i = types2.iterator(); i.hasNext(); ) {
                String s = (String)i.next();
                s += "[]";
                types.add(s);
                addToAT(new StringWrapper(s), t);
            }
        }

        String brackets = getArrayBrackets(dim);        
        for (Iterator i = basetypes.iterator(); i.hasNext(); ) {
            String s = (String)i.next();
            s += brackets;
            types.add(s);
            addToAT(new StringWrapper(s), t);
        }

        return types;
    }

    
    private List/*IMethodBinding*/ getConstructors(ASTNode n) {
        ArrayList l = new ArrayList();
        
        ITypeBinding p;
        if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
            p = ((TypeDeclaration)n).resolveBinding();
        }
        else if (n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
            p = ((AnonymousClassDeclaration)n).resolveBinding();
        }
        else {
            throw new RuntimeException("ERROR unsupported type");
            //return null;
        }
        
        IMethodBinding[] methods = p.getDeclaredMethods();
        for (int i = 0; i < methods.length; i++) {
            if (methods[i].isConstructor()) {
               l.add(methods[i]);
            }
        }
        return l;
    }
    
    private List/*MethodWrapper*/ getWrappedConstructors(ASTNode n) {
        ArrayList l = new ArrayList();
        ITypeBinding p;
        if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
            p = ((TypeDeclaration)n).resolveBinding();
        }
        else {
            p = ((AnonymousClassDeclaration)n).resolveBinding();
        }

        IMethodBinding[] methods = p.getDeclaredMethods();
        for (int i = 0; i < methods.length; i++) {
            if (methods[i].isConstructor()) {
               l.add(new MethodWrapper(methods[i]));
            }
        }
        return l;
    }
    
    private boolean hasOuterThis(ITypeBinding binding) {
        // TODO need isclass check?
        return binding.isNested() && binding.isClass() && !isStatic(binding);
    }
    
    
    
    /**
     * Get a set of the keys of all the supertypes of the binding.
     * Supertype includes itself (reflexive).
     * @param binding
     * @return set of keys of the supertypes
     */
    static public Set/*String*/ getSuperTypes(ITypeBinding binding) {
        HashSet s =  new HashSet();
        LinkedList/*ITypeBinding*/ todo = new LinkedList();
        
        todo.addLast(binding);
        do {
            binding = (ITypeBinding)todo.removeFirst();
            if (s.add(binding.getKey())) {          
                todo.addAll(Arrays.asList(binding.getInterfaces()));
                ITypeBinding sprclass = binding.getSuperclass(); 
                if (sprclass != null) todo.addLast(sprclass);
            }
        } while (!todo.isEmpty());
        
        return s;
    }
    
    
    
    private void loadFieldDomains() {
        String fname = loadPath + "fielddomains.pa";
        BufferedReader in = null;
        try {
            in = new BufferedReader(new FileReader(fname));
            String line;

            while ((line = in.readLine()) != null) {
                if (line.startsWith("#")) continue;
                    
                String[] tuple = line.split("\\s"); // (V, bits, mapname)
                line = tuple[0];
                long size = Long.parseLong(tuple[1]);
                int bits = 1;
                while ((size >> bits) != 0) {
                    bits ++;
                }
                bits -= 1;
                
                if (line.equals("V")) {
                    V_BITS = bits;
                }
                else if (line.equals("I")) {
                    I_BITS = bits;
                }
                else if (line.equals("H")) {
                    H_BITS = bits;   
                }
                else if (line.equals("Z")) {
                    Z_BITS = bits;
                }
                else if (line.equals("F")) {
                    F_BITS = bits;
                }
                else if (line.equals("T")) {
                    T_BITS = bits;
                }
                else if (line.equals("N")) {
                    N_BITS = bits;
                }
                else if (line.equals("M")) {
                    M_BITS = bits;
                }
                else if (line.equals("TV")) {
                    TV_BITS = bits;
                }
            }
        } catch (IOException e1) {
        }
        try {
            if (in != null) in.close();
        } catch (IOException e) {
        }
    }
}
