/*
 * Created on Jun 24, 2004
 */
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.*;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.IndexMap;
import org.sf.bddbddb.util.SystemProperties;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;

/**
 * Derive input relations directly from source using the Eclipse AST package.
 * 
 * @author jimz
 */
public class PAFromSource {
    PrintStream out = System.out;
    
    boolean TRACE_RELATIONS = !System.getProperty("pas.tracerelations", "no").equals("no");
    boolean UNIFY_STRING_CONSTS = !System.getProperty("pas.unifystringconsts", "yes").equals("no");
    
    IndexMap Vmap;
    IndexMap Imap;
    IndexMap Hmap;
    IndexMap Fmap;
    IndexMap Tmap;
    IndexMap Nmap;
    IndexMap Mmap;
    //PathNumbering vCnumbering; // for context-sensitive
    //PathNumbering hCnumbering; // for context-sensitive
    //PathNumbering oCnumbering; // for object-sensitive
    
    static int bddnodes = Integer.parseInt(System.getProperty("bddnodes", "100000"));
    static int bddcache = Integer.parseInt(System.getProperty("bddcache", "10000"));
    static BDDFactory bdd = BDDFactory.init(bddnodes, bddcache);
    
    static BDDDomain V1, V2, I, H1, Z, F, T1, T2, M, N; // H2, M2
    //BDDDomain V1c[], V2c[], H1c[], H2c[];
    
    static int V_BITS=18, I_BITS=16, H_BITS=15, Z_BITS=5, F_BITS=13, T_BITS=12, N_BITS=13, M_BITS=14;
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
    //BDD cha;    // T2xNxM, class hierarchy information  (no context)
    BDD actual; // IxZxV2, actual parameters            (no context)
    BDD formal; // MxZxV1, formal parameters            (no context)
    BDD Iret;   // IxV1, invocation return value        (no context)
    BDD Mret;   // MxV2, method return value            (no context)
    BDD Ithr;   // IxV1, invocation thrown value        (no context)
    BDD Mthr;   // MxV2, method thrown value            (no context)
    BDD mI;     // MxIxN, method invocations            (no context)
    //BDD mV;     // MxV, method variables                (no context)
    //BDD sync;   // V, synced locations                  (no context)

    //BDD fT;     // FxT2, field types                    (no context)
    //BDD fC;     // FxT2, field containing types         (no context)

    //BDD hP;     // H1xFxH2, heap points-to              (+context)
    BDD IE;     // IxM, invocation edges                (no context)
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
    static BDD V1set, V2set, H1set, T1set, T2set, Fset, Mset, Iset, Nset, Zset; //H2set, 
    static BDD V1V2set, V1Fset, V2Fset, V1FV2set, V1H1set, H1Fset; //, H2Fset, H1H2set, H1FH2set
    static BDD IMset, INset, INH1set, INT2set, T2Nset, MZset;
    //BDD V1cset, V2cset, H1cset, H2cset, V1cV2cset, V1cH1cset, H1cH2cset;
    //BDD V1cdomain, V2cdomain, H1cdomain, H2cdomain;

    static int bddminfree = Integer.parseInt(System.getProperty("bddminfree", "20"));
    static String varorder = System.getProperty("bddordering");
    //int MAX_PARAMS = Integer.parseInt(System.getProperty("pas.maxparams", "4"));
    static boolean reverseLocal = System.getProperty("bddreverse", "true").equals("true"); 
    
    static {
        initBDDFactory();
    }
        
    //MultiMap constructors /*<String(class key), Name(constructor)>*/ 
                      //  = new GenericMultiMap();
    
    private static void initBDDFactory() {
        //USE_VCONTEXT = VC_BITS > 0;
        //USE_HCONTEXT = HC_BITS > 0;
        
        //if (USE_VCONTEXT || USE_HCONTEXT) 
        //  bddnodes *= 2;

        bdd.setMaxIncrease(bddnodes/4);
        bdd.setMinFreeNodes(bddminfree);

        V1 = makeDomain("V1", V_BITS);
        V2 = makeDomain("V2", V_BITS);
        I = makeDomain("I", I_BITS);
        H1 = makeDomain("H1", H_BITS);
        //H2 = makeDomain("H2", H_BITS);
        Z = makeDomain("Z", Z_BITS);
        F = makeDomain("F", F_BITS);
        T1 = makeDomain("T1", T_BITS);
        T2 = makeDomain("T2", T_BITS);
        N = makeDomain("N", N_BITS);
        M = makeDomain("M", M_BITS);
        //M2 = makeDomain("M2", M_BITS);

        /*
        if (CONTEXT_SENSITIVE || OBJECT_SENSITIVE || THREAD_SENSITIVE) {
            V1c = new BDDDomain[1];
            V2c = new BDDDomain[1];
            V1c[0] = makeDomain("V1c", VC_BITS);
            V2c[0] = makeDomain("V2c", VC_BITS);
        } else if (CARTESIAN_PRODUCT && false) {
            V1c = new BDDDomain[MAX_PARAMS];
            V2c = new BDDDomain[MAX_PARAMS];
            for (int i = 0; i < V1c.length; ++i) {
                V1c[i] = makeDomain("V1c"+i, H_BITS + HC_BITS);
            }
            for (int i = 0; i < V2c.length; ++i) {
                V2c[i] = makeDomain("V2c"+i, H_BITS + HC_BITS);
            }
        } else {
            V1c = V2c = new BDDDomain[0];
        }
        if (USE_HCONTEXT) {
            H1c = new BDDDomain[] { makeDomain("H1c", HC_BITS) };
            H2c = new BDDDomain[] { makeDomain("H2c", HC_BITS) };
        } else {
            H1c = H2c = new BDDDomain[0];
        }
        */
        
        //if (TRACE) out.println("Variable context domains: "+V1c.length);
        //if (TRACE) out.println("Heap context domains: "+H1c.length);
        
        if (varorder == null) {
            // default variable orderings.
            /*
            if (CONTEXT_SENSITIVE || THREAD_SENSITIVE || OBJECT_SENSITIVE) {
                if (HC_BITS > 0) {
                    varorder = "N_F_Z_I_M2_M_T1_V2xV1_V2cxV1c_H2xH2c_T2_H1xH1c";
                } else {
                    //varorder = "N_F_Z_I_M2_M_T1_V2xV1_V2cxV1c_H2_T2_H1";
                    varorder = "N_F_I_M2_M_Z_V2xV1_V2cxV1c_T1_H2_T2_H1";
                }
            } else if (CARTESIAN_PRODUCT && false) {
                varorder = "N_F_Z_I_M2_M_T1_V2xV1_T2_H2xH1";
                for (int i = 0; i < V1c.length; ++i) {
                    varorder += "xV1c"+i+"xV2c"+i;
                }
            } else {
                //varorder = "N_F_Z_I_M2_M_T1_V2xV1_H2_T2_H1";
                varorder = "N_F_I_M2_M_Z_V2xV1_T1_H2_T2_H1";
            } */
            varorder = "N_F_I_M_Z_V2xV1_T1_T2_H1";
        }
        
        System.out.println("Using variable ordering "+varorder);
        int[] ordering = bdd.makeVarOrdering(reverseLocal, varorder);
        bdd.setVarOrder(ordering);
        
        /*
        V1ctoV2c = bdd.makePair();
        V1ctoV2c.set(V1c, V2c);
        V1cV2ctoV2cV1c = bdd.makePair();
        V1cV2ctoV2cV1c.set(V1c, V2c);
        V1cV2ctoV2cV1c.set(V2c, V1c);
        if (OBJECT_SENSITIVE) {
            V1cH1ctoV2cV1c = bdd.makePair();
            V1cH1ctoV2cV1c.set(V1c, V2c);
            V1cH1ctoV2cV1c.set(H1c, V1c);
        }
        T2toT1 = bdd.makePair(T2, T1);
        T1toT2 = bdd.makePair(T1, T2);
        V1toV2 = bdd.makePair();
        V1toV2.set(V1, V2);
        V1toV2.set(V1c, V2c);
        V2toV1 = bdd.makePair();
        V2toV1.set(V2, V1);
        V2toV1.set(V2c, V1c);
        H1toH2 = bdd.makePair();
        H1toH2.set(H1, H2);
        H1toH2.set(H1c, H2c);
        H2toH1 = bdd.makePair();
        H2toH1.set(H2, H1);
        H2toH1.set(H2c, H1c);
        V1H1toV2H2 = bdd.makePair();
        V1H1toV2H2.set(V1, V2);
        V1H1toV2H2.set(H1, H2);
        V1H1toV2H2.set(V1c, V2c);
        V1H1toV2H2.set(H1c, H2c);
        V2H2toV1H1 = bdd.makePair();
        V2H2toV1H1.set(V2, V1);
        V2H2toV1H1.set(H2, H1);
        V2H2toV1H1.set(V2c, V1c);
        V2H2toV1H1.set(H2c, H1c);
        */
        
        V1set = V1.set();
        /*
        if (V1c.length > 0) {
            V1cset = bdd.one();
            V1cdomain = bdd.one();
            for (int i = 0; i < V1c.length; ++i) {
                V1cset.andWith(V1c[i].set());
                V1cdomain.andWith(V1c[i].domain());
            }
            V1set.andWith(V1cset.id());
        }
        */
        V2set = V2.set();
        /*
        if (V2c.length > 0) {
            V2cset = bdd.one();
            V2cdomain = bdd.one();
            for (int i = 0; i < V2c.length; ++i) {
                V2cset.andWith(V2c[i].set());
                V2cdomain.andWith(V2c[i].domain());
            }
            V2set.andWith(V2cset.id());
        }
        */
        H1set = H1.set();
        /*
        if (H1c.length > 0) {
            H1cset = bdd.one();
            H1cdomain = bdd.one();
            for (int i = 0; i < H1c.length; ++i) {
                H1cset.andWith(H1c[i].set());
                H1cdomain.andWith(H1c[i].domain());
            }
            H1set.andWith(H1cset.id());
        }
        H2set = H2.set();
        if (H2c.length > 0) {
            H2cset = bdd.one();
            H2cdomain = bdd.one();
            for (int i = 0; i < H2c.length; ++i) {
                H2cset.andWith(H2c[i].set());
                H2cdomain.andWith(H2c[i].domain());
            }
            H2set.andWith(H2cset.id());
        }
        */
        T1set = T1.set();
        T2set = T2.set();
        Fset = F.set();
        Mset = M.set();
        Nset = N.set();
        Iset = I.set();
        Zset = Z.set();
        /*
        V1cV2cset = (V1c.length > 0) ? V1cset.and(V2cset) : bdd.zero();
        H1cH2cset = (H1c.length > 0) ? H1cset.and(H2cset) : bdd.zero();
        if (V1c.length > 0) {
            V1cH1cset = (H1c.length > 0) ? V1cset.and(H1cset) : V1cset;
        } else {
            V1cH1cset = (H1c.length > 0) ? H1cset : bdd.zero();
        }*/
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
    }

    static BDDDomain makeDomain(String name, int bits) {
        Assert._assert(bits < 64);
        BDDDomain d = bdd.extDomain(new long[] { 1L << bits })[0];
        d.setName(name);
        return d;
    }
    
    public void resetBDDs() {
        A = bdd.zero();
        vP = bdd.zero();
        S = bdd.zero();
        L = bdd.zero();
        vT = bdd.zero();
        hT = bdd.zero();
        aT = bdd.zero();
        /*
        if (FILTER_HP) {
            fT = bdd.zero();
            fC = bdd.zero();
        }
        
        */
        actual = bdd.zero();
        formal = bdd.zero();
        Iret = bdd.zero();
        Mret = bdd.zero();
        Ithr = bdd.zero();
        Mthr = bdd.zero();
        mI = bdd.zero();
        //mV = bdd.zero();
        //sync = bdd.zero();
        IE = bdd.zero();
        //hP = bdd.zero();
        //visited = bdd.zero();
        /*
        if (OBJECT_SENSITIVE || CARTESIAN_PRODUCT) staticCalls = bdd.zero();
        
        if (THREAD_SENSITIVE) threadRuns = bdd.zero();
        
        if (INCREMENTAL1) {
            old1_A = bdd.zero();
            old1_S = bdd.zero();
            old1_L = bdd.zero();
            old1_vP = bdd.zero();
            old1_hP = bdd.zero();
        }
        if (INCREMENTAL2) {
            old2_myIE = bdd.zero();
            old2_visited = bdd.zero();
        }
        if (INCREMENTAL3) {
            old3_t3 = bdd.zero();
            old3_vP = bdd.zero();
            old3_t4 = bdd.zero();
            old3_hT = bdd.zero();
            old3_t6 = bdd.zero();
            old3_t9 = new BDD[MAX_PARAMS];
            for (int i = 0; i < old3_t9.length; ++i) {
                old3_t9[i] = bdd.zero();
            }
        }
        
        if (CARTESIAN_PRODUCT && false) {
            H1toV1c = new BDDPairing[MAX_PARAMS];
            V1ctoH1 = new BDDPairing[MAX_PARAMS];
            V1csets = new BDD[MAX_PARAMS];
            V1cH1equals = new BDD[MAX_PARAMS];
            for (int i = 0; i < MAX_PARAMS; ++i) {
                H1toV1c[i] = bdd.makePair(H1, V1c[i]);
                V1ctoH1[i] = bdd.makePair(V1c[i], H1);
                V1csets[i] = V1c[i].set();
                V1cH1equals[i] = H1.buildEquals(V1c[i]);
            }
        }
        
        if (USE_VCONTEXT) {
            IEcs = bdd.zero();
        }
        */
    }
        
    class ASTNodeWrapper {
        private ASTNode n; // null for global this or implicit this
        
        ASTNodeWrapper(ASTNode obj) {
            n = obj;
            // peel off parens
            if (obj != null) { 
                n = stripParens(n);
                
                if (n.getNodeType() == ASTNode.THIS_EXPRESSION 
                    && !(this instanceof ThisWrapper)) {
                    out.println("ERROR: this shouldn't be added to astnodewrapper");
                }                
                else if (n.getNodeType() == ASTNode.FIELD_ACCESS) {
                    n = ((FieldAccess)n).getName();
                }
                else if (n.getNodeType() == ASTNode.SUPER_FIELD_ACCESS) {
                    n = ((SuperFieldAccess)n).getName();
                }
                else if (n.getNodeType() == ASTNode.QUALIFIED_NAME) {
                    n = ((QualifiedName)n).getName();
                }
            }
        }
        
        public ASTNode getNode() { return n; } 
        
        public String toString() {
            String s;
            if (n.getNodeType() == ASTNode.SIMPLE_NAME) {
                s = ((SimpleName)n).getFullyQualifiedName();
            }
            else s = n.toString();
            return "NODE: " + n.getNodeType() + ", " + s;
        }
        public boolean equals(Object o) {
            if (o instanceof ASTNodeWrapper) {
                ASTNodeWrapper rhs = (ASTNodeWrapper) o;
                ASTNode m = rhs.n;
                if (m == n) return true;
                if (m == null || n == null) return false;
                if (m.getAST() != n.getAST()) {
                    System.out.println("NODE equals: m.AST != n.AST");
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
                        System.out.println("NODE equals: " 
                                + m.toString() +" != "+ n.toString());
                        return false; // since m != n
                    case ASTNode.SIMPLE_NAME:
                        String nName = ((Name) n).resolveBinding().getKey();
                        String mName = ((Name) m).resolveBinding().getKey();
                        return nName.equals(mName);
                    case ASTNode.STRING_LITERAL:
                        if (UNIFY_STRING_CONSTS) {
                            String mVal = ((StringLiteral)m).getLiteralValue();
                            String nVal = ((StringLiteral)n).getLiteralValue();
                            return mVal.equals(nVal);
                        }
                        return false;
                    case ASTNode.INFIX_EXPRESSION:    
                        if (((InfixExpression) m).resolveTypeBinding().isPrimitive()) {
                            out.println("ERROR: primitive type infix expr");
                        }
                        return false; // treated as new stmt
                    case ASTNode.ASSIGNMENT:
                        if (((Assignment) m).getOperator() != Assignment.Operator.PLUS_ASSIGN
                            || ((Assignment) m).resolveTypeBinding().isPrimitive()) {
                            out.println("ERROR: primitive type assignment or wrong operator");
                        }
                        return false;
                    case ASTNode.PARENTHESIZED_EXPRESSION:
                        out.println("ERROR: parens in astnodewrapper");
                        return false;
                    case ASTNode.THIS_EXPRESSION:
                        out.println("ERROR: this method shouldn't be called");
                        return false;
                    case ASTNode.SUPER_FIELD_ACCESS:  
                    case ASTNode.FIELD_ACCESS:
                    case ASTNode.QUALIFIED_NAME:
                        System.out.println("ERROR: this node shouldn't be here");
                        return false;
                    default:
                        System.out.println("Unhandled equals case: " + m);
                }                
                return false;
            }
            return false;
        }
        
        public int hashCode() {
            if (n == null) return 0;
            return n.hashCode();
        }
    }
    
    
    class ThisWrapper extends ASTNodeWrapper {
        IMethodBinding method;
                
        ThisWrapper(IMethodBinding binding, ThisExpression n) {
            super(n);
            method = binding;
        }
        
        ThisWrapper(MethodDeclaration decl, ThisExpression n) {
            super(n);
            method = decl.resolveBinding();
        }
        
        public String toString() {
            return "THIS: " + method.getKey();
        }
        
        public boolean equals(Object o) {
            if (o instanceof ThisWrapper) {
                return method.getKey().equals(((ThisWrapper) o).method.getKey());
            }
            return false;
        }
        
        public int hashCode() { // doesn't depend on the thisexpression
            //if (method == null) return 0;
            return method.getKey().hashCode();
        }
        
        public IMethodBinding getBinding() {
            return method;
        }
    }
    
    // note unlike other wrappers, this one uses qualified name, not binding key
    class TypeWrapper extends ASTNodeWrapper {
        ITypeBinding type; // might need to switch to Type in JLS3
        TypeWrapper(ITypeBinding binding) {
            super(null);
            type = binding;
        }
        
        public String toString() {
            return "TYPE NODE: " + type.getQualifiedName();
        }
        
        public boolean equals(Object o) {
            if (o instanceof TypeWrapper) {
                return ((TypeWrapper)o).type.getQualifiedName().equals(type.getQualifiedName());
            }
            else if (o instanceof StringWrapper) {
                return type.getQualifiedName().equals(((StringWrapper)o).name);
            }
            return false;
        }
        
        public int hashCode() { // doesn't depend on the thisexpression
            return type.getQualifiedName().hashCode();
        }
        
        public ITypeBinding getBinding() {
            return type;
        }
    }
    
    class MethodWrapper extends ASTNodeWrapper {
        IMethodBinding method; 
        MethodWrapper(IMethodBinding binding) {
            super(null);
            method = binding;
        }
        
        MethodWrapper(MethodDeclaration m) {
            super(null);
            method = m.resolveBinding();
        }
        
        public String toString() {
            return "METHOD NODE: " + method.getKey();
        }
        
        public boolean equals(Object o) {
            if (o instanceof MethodWrapper) {
                return ((MethodWrapper)o).method.getKey().equals(method.getKey());
            }
            return false;
        }
        
        public int hashCode() { // doesn't depend on the thisexpression
            return method.getKey().hashCode();
        }
    }
    
    
    class StringWrapper extends ASTNodeWrapper {
        String name;
        StringWrapper(String s) {
            super(null);
            name = s;
        }
        
        public String toString() {
            return "NODE: " + name;
        }
        
        public boolean equals(Object o) {
            if (o instanceof StringWrapper) {
                return ((StringWrapper)o).name.equals(name);
            }
            else if (o instanceof TypeWrapper) {
                return ((TypeWrapper)o).type.getKey().equals(name);
            }
            return false;
        }
        
        public int hashCode() {
            return name.hashCode();
        }
        
        public String getString() {
            return name;
        }
    }

    TypeWrapper CLONEABLE = null;
    TypeWrapper OBJECT = null;
    TypeWrapper SERIALIZABLE = null;
    TypeWrapper STRING = null;
    
    final StringWrapper GLOBAL_THIS = new StringWrapper("GlobalThis"); 
    final StringWrapper ARRAY_FIELD = new StringWrapper("ArrayField");
    
    ASTNode stripParens(ASTNode n) {
        while (n.getNodeType() == ASTNode.PARENTHESIZED_EXPRESSION) {
            n = ((ParenthesizedExpression) n).getExpression();
        }
        return n;
    }
    
    /**
     * @author jimz
     */
    class PAASTVisitor extends ASTVisitor {
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
        
        // TODO handle super.this
        // TODO handle <clinit>
        
        /*
        public PAASTVisitor(int i, int s) {
            super(false); // avoid comments
            id = i;
            scope = s;
        }
         */
        public PAASTVisitor() { super(false); /*this(0,0);*/};
        
        // vP, hT, vT
        public boolean visit(ArrayCreation arg0) {
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            addToVP(node, node);
            return true;
        }
        public boolean visit(StringLiteral arg0) {
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            addToVP(node, node);          
            return true;
        }
        public boolean visit(InfixExpression arg0) {
            return true;
        }
        public void endVisit(InfixExpression arg0) {
            if (arg0.resolveTypeBinding().isPrimitive()) return;
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            addToVP(node, node);
        }
        // vP, hT, vT, actual, Mthr, Iret, Ithr, mI, IE0
        public boolean visit(ClassInstanceCreation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            addToVP(n, n);
            
            IMethodBinding method = arg0.resolveConstructorBinding();

            MethodDeclaration m = (MethodDeclaration)findDeclaringParent(arg0);
            ASTNodeWrapper thisParam;
            ASTNodeWrapper name = new StringWrapper(method.getName());
            
            Expression expr = arg0.getExpression();
            ThisExpression t = null;
            if (expr != null && (t = getThis(expr)) == null) {
                thisParam = new ASTNodeWrapper(expr);
            }
            else { // implicit this or expr is thisexpr
                thisParam = new ThisWrapper(m, t); 
            }
  
            List args = arg0.arguments();
            addMethodInvocation(thisParam, n, method, args, m, name);
            return true;
        }
        
        // A, vP, vT, hT
        public boolean visit(Assignment arg0) {
            arg0.getRightHandSide().accept(this);
            return false; // ignore left side
        }
        public void endVisit(Assignment arg0) {
            Expression right = arg0.getRightHandSide();  
            Expression left = arg0.getLeftHandSide();            
            ITypeBinding rType = right.resolveTypeBinding();
            if (rType == null) { 
                out.println("bindings unresolved... this shouldn't happen...");
                throw new RuntimeException("unresolved bindings");
            }
            else {
                if (rType.isPrimitive() || rType.isNullType()) return;
                // string +=
                if (arg0.getOperator() == Assignment.Operator.PLUS_ASSIGN) {
                    addToVP(new ASTNodeWrapper(left), 
                            new ASTNodeWrapper(arg0));
                }
                else compareAssignment(left, right);
            } 
        }
        
        // A, S, vT
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
                    storeToQualifiedField(arr, ARRAY_FIELD, right);
                    return;
                case ASTNode.SUPER_FIELD_ACCESS:
                    // TODO store to super
                    out.println("ERROR: super field access to be handled" + left);
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
                        storeToStaticField(qa, right);
                    }
                    else { // treat as field access
                        storeToQualifiedField(left, qa, right);
                    }
                    return;
                case ASTNode.FIELD_ACCESS:
                    FieldAccess fa = (FieldAccess)left;
                    left = fa.getExpression();
                    left.accept(this); // to handle x.y.z = stuff;
                    if (isStatic(fa.getName())) {
                        storeToStaticField(fa, right);
                    }
                    else {
                        ThisExpression t = getThis(left);
                        if (t == null) { // store
                            storeToQualifiedField(left, fa, right);
                        }
                        else { // left = this 
                            storeToThisField(t, fa, right);
                        }
                    }
                    return;
                case ASTNode.SIMPLE_NAME:
                    // out.println(left + " = " + right + " field? " + isField((Name)left));
                    if (isField((Name)left)) { // implicit this?
                        // store                        
                        if (isStatic((Name)left)) {
                            storeToStaticField(left, right);
                        }
                        else {
                            storeToThisField(null, left, right);
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
            Expression field, Expression rhs) {
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
                    addToS(t, field, 
                        new ASTNodeWrapper(rhs));  
                    return;
                case ASTNode.THIS_EXPRESSION:
                    addToS(t, field, 
                        (ThisExpression)rhs);
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }
        }

        private void storeToQualifiedField(Expression qualifier, 
            Expression field, Expression rhs) {
            storeToQualifiedField(qualifier, new ASTNodeWrapper(field), rhs);
        }
        
        private void storeToQualifiedField(Expression qualifier, 
            ASTNodeWrapper field, Expression rhs) {
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
                    addToS(new ASTNodeWrapper(qualifier), field, 
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

        private void storeToStaticField(Expression field, Expression rhs) {
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
                    addToS(GLOBAL_THIS, 
                        new ASTNodeWrapper(field), new ASTNodeWrapper(rhs));  
                    return;
                case ASTNode.THIS_EXPRESSION:
                    addToS(GLOBAL_THIS, 
                        new ASTNodeWrapper(field), (ThisExpression)rhs);
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }    
        }

        // formal, vT
        public boolean visit(MethodDeclaration arg0) { 
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
                        
            if (arg0.getBody() != null) arg0.getBody().accept(this);
            
            return false; // do not go into the decls
        }

        // L, vT
        public boolean visit(FieldAccess arg0) {
            arg0.getExpression().accept(this);
            if (!arg0.resolveTypeBinding().isPrimitive()) {
                // load
                Name f = arg0.getName();  
                if (isStatic(f)) {
                    addToL(GLOBAL_THIS, f, arg0);
                }
                else {
                    ThisExpression t = getThis(arg0.getExpression());
                    if (t != null) {
                        addToL(t, f, new ASTNodeWrapper(arg0));
                    }
                    else {
                        addToL(new ASTNodeWrapper(arg0.getExpression()), f, arg0);
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
                            addToL(GLOBAL_THIS, arg0, arg0);
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
                    addToL(GLOBAL_THIS, arg0, arg0);
                }
                else { // treat as field
                    ThisExpression t = getThis(arg0.getQualifier());
                    if (t != null) {
                        addToL(t, arg0, new ASTNodeWrapper(arg0));
                    }
                    else {
                        addToL(new ASTNodeWrapper(arg0.getQualifier()), 
                            arg0, arg0);
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
                addToL(new ASTNodeWrapper(arg0.getArray()), 
                        ARRAY_FIELD, new ASTNodeWrapper(arg0));
            }
        }
        
        // aT
        public boolean visit(AnonymousClassDeclaration arg0) {
            addBindingToAT(arg0.resolveBinding());
            return true;
        }
        
        // aT, formal
        public boolean visit(TypeDeclaration arg0) {
            addBindingToAT(arg0.resolveBinding()); 
            
            ITypeBinding classBinding = arg0.resolveBinding();
            IMethodBinding[] bindings = classBinding.getDeclaredMethods();
            for (int i = 0; i < bindings.length; i++) {
                ASTNodeWrapper thisParam;
                if (isStatic(bindings[i])) {
                    thisParam = GLOBAL_THIS;
                }
                else {
                    thisParam = new ThisWrapper(bindings[i], null);
                }
                
                int M_i = Mmap.get(new MethodWrapper(bindings[i]));
                BDD M_bdd = M.ithVar(M_i);
                addToFormal(M_bdd, 0, thisParam);
                M_bdd.free();
            }
            return true;
        }
        
        // Mret
        public boolean visit(ReturnStatement arg0) {
            return true;
        }   
        public void endVisit(ReturnStatement arg0) {
            Expression e = arg0.getExpression();
            ITypeBinding binding = e.resolveTypeBinding();
            if (binding.isPrimitive() || binding.isNullType()) return;
            
            MethodDeclaration m = (MethodDeclaration)findDeclaringParent(arg0);
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
            MethodDeclaration m = findThrowParent(arg0, 
                arg0.getExpression().resolveTypeBinding());
            
            if (m == null) return;
            addMThrow(m, arg0.getExpression());
        }
        private void addMThrow(MethodDeclaration m, Expression e) {
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
                    addToMthr(m, new ThisWrapper(m, (ThisExpression)e));
                    return;
                default:
                    // e.g. nullexpr, do nothing
            }
        }
        
        // 
        
        
        /**
         * @param n Node from where to start searching for parent 
         *          (does not look at itself)
         * @param ex Exception being thrown.
         * @return returns null if exception is caught, 
         *          otherwise return method that throws it
         */
        private MethodDeclaration findThrowParent(ASTNode n, ITypeBinding ex) {
            ASTNode prev;
            do {
                prev = n;
                n = n.getParent();
            } while (!(n instanceof MethodDeclaration 
                    || n instanceof TryStatement));
            
            if (n instanceof MethodDeclaration) return (MethodDeclaration)n;
            
            TryStatement t = (TryStatement)n;
            // n in finally?
            if (prev == t.getFinally()) return findThrowParent(t, ex); 
            
            List catches = t.catchClauses();
            for (Iterator i = catches.iterator(); i.hasNext();) {
                Type type = ((CatchClause)i.next()).getException().getType();
                
                if (getSuperTypes(ex).contains(type.resolveBinding().getKey())) {
                    return null; // exception caught
                }
            }
            
            return findThrowParent(t, ex); // exception uncaught
        }
        
        /**
         * Get a set of the keys of all the supertypes of the binding.
         * Supertype includes itself (reflexive).
         * @param binding
         * @return
         */
        private Set/*String*/ getSuperTypes(ITypeBinding binding) {
            HashSet s =  new HashSet();
            LinkedList/*ITypeBinding*/ todo = new LinkedList();
            
            todo.addLast(binding);
            do {
                binding = (ITypeBinding)todo.removeFirst();
                if (s.add(binding.getKey())) {          
                    todo.addAll(Arrays.asList(binding.getInterfaces()));
                    todo.addLast(binding.getSuperclass());
                }
            } while (!todo.isEmpty());
            
            return s;
        }
        
        // actual, Mthr, Iret, Ithr, IE0, mI
        public boolean visit(MethodInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveMethodBinding();
            
            MethodDeclaration m = (MethodDeclaration)findDeclaringParent(arg0);
            ASTNodeWrapper thisParam;
            SimpleName name = null;
            if (isStatic(method)) {
                thisParam = GLOBAL_THIS;
                
                addToIE(n, method);
            }
            else {
                Expression expr = arg0.getExpression();
                ThisExpression t = null;
                if (expr != null && (t = getThis(expr)) == null) {
                    thisParam = new ASTNodeWrapper(expr);
                }
                else { // implicit this or expr is thisexpr
                    thisParam = new ThisWrapper(m, t); 
                }
                name = arg0.getName();
            }
            List args = arg0.arguments();
            addMethodInvocation(thisParam, n, method, args, 
                m, new ASTNodeWrapper(name));
            
            return true; 
        }

        public boolean visit(SuperMethodInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveMethodBinding();
            
            MethodDeclaration m = (MethodDeclaration)findDeclaringParent(arg0);
            ASTNodeWrapper thisParam;
            if (isStatic(method)) {
                thisParam = GLOBAL_THIS;
            }
            else {
                // TODO need super this
                thisParam = GLOBAL_THIS; // change this
            }

            addToIE(n, method);
            
            List args = arg0.arguments();
            addMethodInvocation(thisParam, n, method, 
                args, m, new ASTNodeWrapper(null));
            
            return true;
        }


        public boolean visit(ConstructorInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveConstructorBinding();
            
            MethodDeclaration m = (MethodDeclaration)findDeclaringParent(arg0);
            ASTNodeWrapper name = new StringWrapper(method.getName());
            List args = arg0.arguments();
            addMethodInvocation(new ThisWrapper(m, null), n, method, args, m, name);
            return true; 
        }
        
        public boolean visit(SuperConstructorInvocation arg0) {
            ASTNodeWrapper n = new ASTNodeWrapper(arg0);
            IMethodBinding method = arg0.resolveConstructorBinding();

            MethodDeclaration m = (MethodDeclaration)findDeclaringParent(arg0);
            ASTNodeWrapper thisParam;
            ASTNodeWrapper name = new StringWrapper(method.getName());
            
            Expression expr = arg0.getExpression();
            ThisExpression t = null;
            if (expr != null && (t = getThis(expr)) == null) {
                thisParam = new ASTNodeWrapper(expr);
            }
            else { // implicit this or expr is thisexpr
                thisParam = new ThisWrapper(m, t); 
            }
  
            List args = arg0.arguments();
            addMethodInvocation(thisParam, n, method, args, m, name);
            
            return true; 
        }

        private void addMethodInvocation(ASTNodeWrapper thisParam, 
                ASTNodeWrapper invocation, IMethodBinding invocationBinding, 
                List args, MethodDeclaration enclosingMethod, 
                ASTNodeWrapper methodName) {
            // Mthr
            ITypeBinding[] exs = invocationBinding.getExceptionTypes();
            for (int i = 0; i < exs.length; i++) {
                MethodDeclaration m = 
                                findThrowParent(invocation.getNode(), exs[i]);            
                if (m != null) {
                    addToMthr(m, invocation);
                }                
            }
            
            int I_i = Imap.get(invocation);
            BDD I_bdd = I.ithVar(I_i);
            addToActual(I_bdd, 0, thisParam);
            
            Iterator it = args.iterator();
            for (int i = 1; it.hasNext(); i++) {
                Expression arg = (Expression)it.next();
                ITypeBinding argBinding = arg.resolveTypeBinding();
                if (argBinding.isPrimitive() || argBinding.isNullType()) continue;
                addToActual(I_bdd, i, new ASTNodeWrapper(arg));
            }
            
            ITypeBinding retType = invocationBinding.getReturnType();
            if (!retType.isPrimitive()) addToIret(I_bdd, invocation);
            //addToIthr(I_bdd, invocation); 
            // TODO add Ithr
            addToMI(enclosingMethod, I_bdd, methodName);
            
            I_bdd.free();
        }
        
        public void postVisit(ASTNode arg0) {
        }
        public void preVisit(ASTNode arg0) {
            //out.println(arg0);
        }
        

        public boolean visit(SuperFieldAccess arg0) {
            // TODO Auto-generated method stub
            // load
            return false;// do not go into simplename
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
            return true;
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
        public boolean visit(Initializer arg0) {
            return true;
        }
        public boolean visit(LabeledStatement arg0) {
            return true;
        }
        public boolean visit(ContinueStatement arg0) {
            return true; 
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
    }
    
    private boolean isField(Name n) {
        IBinding bind = n.resolveBinding();
        if (bind.getKind() == IBinding.VARIABLE) {
            return ((IVariableBinding)bind).isField();
        }
        return false;
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
    
    private boolean isStatic(Name n) {
        return Modifier.isStatic(n.resolveBinding().getModifiers());
    }
    
    private boolean isStatic(IBinding b) {
        return Modifier.isStatic(b.getModifiers());
    }
    
    // Read in default properties.
    static { SystemProperties.read("pas.properties"); }
    
    static boolean USE_JOEQ_CLASSLIBS = !System.getProperty("pas.usejoeqclasslibs", "no").equals("no");

    //Set/*<CompilationUnit>*/ ast;
    List/*<CompilationUnit>*/ todo;
    
    public PAFromSource() {
        todo = new ArrayList();
    }
    
    public static void main(String[] args) throws IOException {
        
        Set files;    
        if (args[0].startsWith("@")) {
            files = readClassesFromFile(args[0].substring(1));
        } else {
            files = new HashSet();
            files.add(args[0]);
        }
        
        PAFromSource dis = new PAFromSource();
     
        dis.run(files);
    }

    
    static Set readClassesFromFile(String fname) 
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
     * @param files
     * @throws IOException
     */
    public void run(Set files) throws IOException {
        System.out.println(files.size() + " files to parse.");
        resetBDDs();
        initializeMaps();

        generateASTs(files);
        
        // Start timing.
        long time = System.currentTimeMillis();
        
        while (!todo.isEmpty()) {
            generateRelations();
        }
        
        // vT, aT
        Iterator it = Vmap.iterator();
        for (int i = 0; it.hasNext(); i++) {
            ASTNodeWrapper v =(ASTNodeWrapper)it.next();
            // note: requires iterator to iterate in order of index
            // otherwise do i=Vmap.get(v) first
            addToVT(i, v); 
            addArrayToAT(v);
        }

        // TODO transitive closure on aT
        
        System.out.println("Time spent generating relations: "+(System.currentTimeMillis()-time)/1000.);
               
        System.out.println("Writing relations...");
        time = System.currentTimeMillis();
        dumpBDDRelations();
        System.out.println("Time spent writing: "+(System.currentTimeMillis()-time)/1000.);
    }

    public void dumpBDDRelations() throws IOException {        
        // difference in compatibility
        BDD S0 = S;//.exist(V1cV2cset);
        BDD L0 = L;//.exist(V1cV2cset);
        BDD IE0 = IE;//.exist(V1cV2cset);
        BDD vP0 = vP;//vP.exist(V1cH1cset);
        
        String dumpPath = System.getProperty("pas.dumppath", "");
        if (dumpPath.length() > 0) {
            File f = new File(dumpPath);
            if (!f.exists()) f.mkdirs();
            String sep = System.getProperty("file.separator", "/");
            if (!dumpPath.endsWith(sep))
                dumpPath += sep;
        }
        System.out.println("Dumping to path "+dumpPath);
        
        DataOutputStream dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"bddinfo"));
            for (int i = 0; i < bdd.numberOfDomains(); ++i) {
                BDDDomain d = bdd.getDomain(i);
                if (d == V1 || d == V2)
                    dos.writeBytes("V\n");
                else if (d == H1)// || d == H2)
                    dos.writeBytes("H\n");
                else if (d == T1 || d == T2)
                    dos.writeBytes("T\n");
                else if (d == F)
                    dos.writeBytes("F\n");
                else if (d == I)
                    dos.writeBytes("I\n");
                else if (d == Z)
                    dos.writeBytes("Z\n");
                /*else if (d == N)
                    dos.writeBytes("N\n");*/
                else if (d == M)// || d == M2)
                    dos.writeBytes("M\n");
                /*else if (Arrays.asList(V1c).contains(d)
                        || Arrays.asList(V2c).contains(d))
                    dos.writeBytes("VC\n");
                else if (Arrays.asList(H1c).contains(d)
                        || Arrays.asList(H2c).contains(d))
                    dos.writeBytes("HC\n");
                else if (DUMP_SSA) {
                    dos.writeBytes(bddIRBuilder.getDomainName(d)+"\n");
                }*/
                else
                    dos.writeBytes(d.toString() + "\n");
            }
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"fielddomains.pa"));
            dos.writeBytes("V "+(1L<<V_BITS)+" var.map\n");
            dos.writeBytes("H "+(1L<<H_BITS)+" heap.map\n");
            dos.writeBytes("T "+(1L<<T_BITS)+" type.map\n");
            dos.writeBytes("F "+(1L<<F_BITS)+" field.map\n");
            dos.writeBytes("I "+(1L<<I_BITS)+" invoke.map\n");
            dos.writeBytes("Z "+(1L<<Z_BITS)+"\n");
            //dos.writeBytes("N "+(1L<<N_BITS)+" name.map\n");
            dos.writeBytes("M "+(1L<<M_BITS)+" method.map\n");
            //dos.writeBytes("VC "+(1L<<VC_BITS)+"\n");
            //dos.writeBytes("HC "+(1L<<HC_BITS)+"\n");
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
        //bdd.save(dumpPath+"cha.bdd", cha);
        bdd.save(dumpPath+"actual.bdd", actual);
        bdd.save(dumpPath+"formal.bdd", formal);
        //bdd.save(dumpPath+"mV.bdd", mV);
        //bdd.save(dumpPath+"mC.bdd", mC);
        //bdd.save(dumpPath+"mI.bdd", mI);
        bdd.save(dumpPath+"Mret.bdd", Mret);
        bdd.save(dumpPath+"Mthr.bdd", Mthr);
        bdd.save(dumpPath+"Iret.bdd", Iret);
        bdd.save(dumpPath+"Ithr.bdd", Ithr);
        bdd.save(dumpPath+"IE0.bdd", IE0);
        //bdd.save(dumpPath+"sync.bdd", sync);
        /*if (threadRuns != null)
            bdd.save(dumpPath+"threadRuns.bdd", threadRuns);
        if (IEfilter != null)
            bdd.save(dumpPath+"IEfilter.bdd", IEfilter);
        bdd.save(dumpPath+"roots.bdd", getRoots());

        if (V1c.length > 0 && H1c.length > 0) {
            bdd.save(dumpPath+"eq.bdd", V1c[0].buildEquals(H1c[0]));
        }
        
        if (DUMP_FLY) {
            initFly();
            bdd.save(dumpPath+"visited.bdd", visitedFly);
            bdd.save(dumpPath+"mS.bdd", mS);
            bdd.save(dumpPath+"mL.bdd", mL);
            bdd.save(dumpPath+"mvP.bdd", mvP);
            bdd.save(dumpPath+"mIE.bdd", mIE);
        }
        */
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"var.map"));
            Vmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"heap.map"));
            Hmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"type.map"));
            Tmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"field.map"));
            Fmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"invoke.map"));
            Imap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        /*
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"name.map"));
            Nmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        */
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"method.map"));
            Mmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }

    }
    
    IndexMap makeMap(String name, int bits) {
        return new IndexMap(name, 1 << bits);
    }

    private void initializeMaps() {
        Vmap = makeMap("Vars", V_BITS);
        Vmap.get(GLOBAL_THIS);
        Imap = makeMap("Invokes", I_BITS);
        Hmap = makeMap("Heaps", H_BITS);
        Fmap = makeMap("Fields", F_BITS);
        Tmap = makeMap("Types", T_BITS);
        Nmap = makeMap("Names", N_BITS);
        Mmap = makeMap("Methods", M_BITS);
        Mmap.get(new StringWrapper("DummyMethod")); 
    }

    private void generateASTs(Set files) {
        long time = System.currentTimeMillis();
        
        for (Iterator i = files.iterator(); i.hasNext(); ) {
            Object o = i.next();
            CompilationUnit cu;
            if (o instanceof String) {
                cu = readSourceFile((String) o);
            } else {
                ASTParser c = ASTParser.newParser(AST.JLS2);
                if (o instanceof ICompilationUnit)
                    c.setSource((ICompilationUnit) o);
                else
                    c.setSource((IClassFile) o);
                c.setResolveBindings(true);
                cu = (CompilationUnit) c.createAST(null);
            }
            if (cu.getMessages().length == 0) {
                todo.add(cu);
            }
            else {
                System.out.println("Parse error. Skipping...");
            }

        }
    
        System.out.println("Time spent parsing: "+(System.currentTimeMillis()-time)/1000.);
    }
    
    
    private void generateRelations() {
        CompilationUnit cu = (CompilationUnit)todo.remove(todo.size()-1);

        //cu.accept(new ConstructorVisitor());
        cu.accept(new PAASTVisitor());  

    }
    
    static CompilationUnit readSourceFile(String fname) {        
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
        
        ASTParser parser = ASTParser.newParser(AST.JLS2); // = ASTParser.newParser(AST.JLS3);
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
    
    void addToVP(ASTNodeWrapper v, ASTNodeWrapper h) {
        int i = Vmap.get(v);
        int V_i = i;
        int H_i = Hmap.get(h);
        addToHT(H_i, h);
        BDD V_bdd = V1.ithVar(V_i);
        BDD bdd1 = H1.ithVar(H_i);
        bdd1.andWith(V_bdd); // .id()?
        //out.println("adding to vP " + v + " / " + h); 
        if (TRACE_RELATIONS) out.println("Adding to vP: "+bdd1.toStringWithDomains());
        vP.orWith(bdd1);
    }
    
    private BodyDeclaration findDeclaringParent(ASTNode n) {
        // walk up tree to find containing method
        while (!((n = n.getParent()) instanceof BodyDeclaration));
        
        if (n instanceof FieldDeclaration || n instanceof Initializer) {
            while (!((n = n.getParent()) instanceof TypeDeclaration));
            return (BodyDeclaration)n;
        }
        else if (n instanceof MethodDeclaration) return (BodyDeclaration)n;
        
        out.println("ERROR: unsupported parent of thisexpr");
        return null;
    }
    
    void addThisToA(ASTNode v1, ThisExpression e) {
        BodyDeclaration n = findDeclaringParent(v1);
        ASTNodeWrapper v = new ASTNodeWrapper(v1);
        if (n instanceof TypeDeclaration) {
            ITypeBinding p = ((TypeDeclaration)n).resolveBinding();
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
        BodyDeclaration n = findDeclaringParent(e1);  
        if (n instanceof TypeDeclaration) {
            ITypeBinding p = ((TypeDeclaration)n).resolveBinding();
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
        BodyDeclaration n = findDeclaringParent(v2);
        ASTNodeWrapper v = new ASTNodeWrapper(v2);  
        if (n instanceof TypeDeclaration) {
            ITypeBinding p = ((TypeDeclaration)n).resolveBinding();
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
        out.println("adding to A " + v1 + " / " + v2); 
        if (TRACE_RELATIONS) out.println("Adding to A: "+bdd1.toStringWithDomains());
        A.orWith(bdd1);
    }
    
    void addToFormal(BDD M_bdd, int z, ASTNodeWrapper v) {
        BDD bdd1 = Z.ithVar(z);
        int V_i = Vmap.get(v);
        bdd1.andWith(V1.ithVar(V_i));
        bdd1.andWith(M_bdd.id());
        if (TRACE_RELATIONS) out.println("Adding to formal: "+bdd1.toStringWithDomains());
        formal.orWith(bdd1);
    }
    
    
    void addToActual(BDD I_bdd, int z, ASTNodeWrapper v) {
        BDD bdd1 = Z.ithVar(z);
        int V_i = Vmap.get(v);
        bdd1.andWith(V2.ithVar(V_i));
        bdd1.andWith(I_bdd.id());
        if (TRACE_RELATIONS) out.println("Adding to actual: "+bdd1.toStringWithDomains());
        actual.orWith(bdd1);
    }

    
    void addToS(ASTNodeWrapper v1, ASTNodeWrapper f, ASTNodeWrapper v2) {
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
    
    void addToS(ThisExpression e, ASTNode f, ASTNodeWrapper v2) {
        BodyDeclaration n = findDeclaringParent(f);
        if (n instanceof TypeDeclaration) {
            ITypeBinding p = ((TypeDeclaration)n).resolveBinding();
            IMethodBinding[] methods = p.getDeclaredMethods();
            for (int i = 0; i < methods.length; i++) {
                if (methods[i].isConstructor()) {
                    addToS(new ThisWrapper(methods[i], e), 
                        new ASTNodeWrapper(f), v2);
                }
            }
        }
        else {// method decl
            addToS(new ThisWrapper((MethodDeclaration)n, e), 
                new ASTNodeWrapper(f), v2);
        }
    }
    
    void addToS(ASTNodeWrapper v1, ASTNodeWrapper f, ThisExpression e) {
        ASTNode startnode = f.getNode();
        if (startnode == null) startnode = v1.getNode();
        if (startnode == null) startnode = e;
        BodyDeclaration n = findDeclaringParent(startnode);
        if (n instanceof TypeDeclaration) {
            ITypeBinding p = ((TypeDeclaration)n).resolveBinding();
            IMethodBinding[] methods = p.getDeclaredMethods();
            for (int i = 0; i < methods.length; i++) {
                if (methods[i].isConstructor()) {
                    addToS(v1, f, new ThisWrapper(methods[i], e));
                }
            }
        }
        else {// method decl
            addToS(v1, f, 
                new ThisWrapper((MethodDeclaration)n, e));
        }
    }
    
    void addToS(ThisExpression e, ASTNode f, ThisExpression e2) {
        BodyDeclaration n = findDeclaringParent(f);
        if (n instanceof TypeDeclaration) {        
            ITypeBinding p = ((TypeDeclaration)n).resolveBinding();
            IMethodBinding[] methods = p.getDeclaredMethods();
            for (int i = 0; i < methods.length; i++) {
                if (methods[i].isConstructor()) {
                    addToS(new ThisWrapper(methods[i], e), 
                        new ASTNodeWrapper(f), 
                        new ThisWrapper(methods[i], e2));
                }
            }
        }
        else {
            MethodDeclaration decl = (MethodDeclaration)n;
            addToS(new ThisWrapper(decl, e), new ASTNodeWrapper(f), 
                    new ThisWrapper(decl, e2));  
        }
    }
    
    void addToL(ASTNodeWrapper v1, ASTNodeWrapper f, ASTNodeWrapper v2) {
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
        
    void addToL(ASTNodeWrapper v1, ASTNode f, ASTNode v2) {
        if (f == v2) {
            ASTNodeWrapper n = new ASTNodeWrapper(f);
            addToL(v1, n, n);
        }
        else addToL(v1, new ASTNodeWrapper(f), new ASTNodeWrapper(v2));        
    }
        
    void addToL(ThisExpression v1, ASTNode f, ASTNodeWrapper v2) {
        BodyDeclaration n = findDeclaringParent(f);
        ASTNodeWrapper fw = (v2.getNode() == f) ? v2 : new ASTNodeWrapper(f);
        
        if (n instanceof TypeDeclaration) {
            ITypeBinding p = ((TypeDeclaration)n).resolveBinding();
            IMethodBinding[] methods = p.getDeclaredMethods();
            for (int i = 0; i < methods.length; i++) {
                if (methods[i].isConstructor()) {
                    addToL(new ThisWrapper(methods[i], v1), fw, v2);   
                }
            }
        }
        else {// method decl
            addToL(new ThisWrapper((MethodDeclaration)n, v1), fw, v2);
        }
    }
    
    
    void addToVT(int V_i, ITypeBinding type) {
        BDD bdd1 = V1.ithVar(V_i);
        int T_i = Tmap.get(new TypeWrapper(type));
        bdd1.andWith(T1.ithVar(T_i));
        if (TRACE_RELATIONS) out.println("Adding to vT: "+bdd1.toStringWithDomains());
        vT.orWith(bdd1);
    }
    
    void addToVT(int V_i, ASTNodeWrapper v) {
        if (v instanceof ThisWrapper) {
            IBinding bind = ((ThisWrapper)v).getBinding();
            switch (bind.getKind()) {
                case IBinding.VARIABLE:
                    addToVT(V_i, ((IVariableBinding)bind).getType());
                    return;
                case IBinding.TYPE:
                    addToVT(V_i, (ITypeBinding)bind);
                    return;
                case IBinding.METHOD:
                    addToVT(V_i, ((IMethodBinding)bind).getDeclaringClass());
                    return;
                default:
                    out.println("ERROR: unhandled binding type " + v);
            }            
        }    
        else if (v instanceof StringWrapper) {
            if (v == GLOBAL_THIS) {
                BDD bdd1 = V1.ithVar(V_i);
                bdd1.andWith(T1.ithVar(0));
                if (TRACE_RELATIONS) out.println("Adding to vT: "+bdd1.toStringWithDomains());
                vT.orWith(bdd1);
            }
            else {
                out.println("ERROR: unhandled stringwrapper node in V: " + v);
            }
        }
        else if (v instanceof TypeWrapper) {
            out.println("ERROR: this type of node shouldn't be in V");
        }
        else if (v.getNode() instanceof Expression) {
            addToVT(V_i, ((Expression)v.getNode()).resolveTypeBinding());
        }    
        else out.println("addToVT: unhandled node type: " + v);
    }

    
    void addToHT(int H_i, ITypeBinding type) {
        int T_i = Tmap.get(type);
        BDD T_bdd = T2.ithVar(T_i);
        BDD bdd1 = H1.ithVar(H_i);
        bdd1.andWith(T_bdd);
        if (TRACE_RELATIONS) out.println("Adding to hT: "+bdd1.toStringWithDomains());
        hT.orWith(bdd1);
    }
    
    
    void addToHT(int H_i, ASTNodeWrapper h) {
        if (h instanceof ThisWrapper || 
            h instanceof StringWrapper || 
            h instanceof TypeWrapper) {
            out.println("ERROR: this type of node shouldn't be in H");
        }
        else {
            if (h.getNode() instanceof Expression) {
                Expression e = (Expression)h.getNode();
                addToHT(H_i, e.resolveTypeBinding());
            }
            else out.println("ERROR: this type of node shouldn't be in H");
        }        
    }
    
    // super, this
    void addToAT(ASTNodeWrapper t1, ASTNodeWrapper t2) {
        int T1_i = Tmap.get(t1);
        int T2_i = Tmap.get(t2);
        BDD T1_bdd = T1.ithVar(T1_i);
        BDD bdd1 = T2.ithVar(T2_i);
        bdd1.andWith(T1_bdd);
        //out.println("Adding to aT: "+ T1_i + " " + t1+" / " + T2_i + " " + t2);
        if (TRACE_RELATIONS) out.println("Adding to aT: "+bdd1.toStringWithDomains());
        aT.orWith(bdd1);
    }
    
    private List addBindingToAT(ITypeBinding binding) {
        List types = new LinkedList();
        TypeWrapper tw = new TypeWrapper(binding);
        addToAT(tw, tw);// reflexive?
        types.add(binding.getQualifiedName());
        ITypeBinding superBinding = binding.getSuperclass();
        if (superBinding != null) {
            //out.println(binding+", Super: " + superBinding);
            addToAT(new TypeWrapper(superBinding), tw);
            types.add(superBinding.getQualifiedName());
        }
        ITypeBinding[] interfaces = binding.getInterfaces();
        for (int i = 0; i < interfaces.length; i++) {
            addToAT(new TypeWrapper(interfaces[i]), tw);
            types.add(interfaces[i].getQualifiedName());
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


    private void addArrayToAT(ASTNodeWrapper w) {
        Expression e = (Expression) w.getNode();
        if (e == null) return;
        ITypeBinding t = e.resolveTypeBinding();
        if (t.isArray()) addArrayToAT(t);
    }

    private void addToMret(MethodDeclaration m, ASTNodeWrapper v) {
        int V_i = Vmap.get(v);
        int M_i = Mmap.get(new MethodWrapper(m));
        BDD M_bdd = M.ithVar(M_i);
        BDD bdd1 = V2.ithVar(V_i);
        bdd1.andWith(M_bdd);
        if (TRACE_RELATIONS) out.println("Adding to Mret: "+bdd1.toStringWithDomains());
        Mret.orWith(bdd1);
        
    }
    
    private void addToMthr(MethodDeclaration m, ASTNodeWrapper v) {
        int V_i = Vmap.get(v);
        int M_i = Mmap.get(new MethodWrapper(m));
        BDD M_bdd = M.ithVar(M_i);
        BDD bdd1 = V2.ithVar(V_i);
        bdd1.andWith(M_bdd);
        if (TRACE_RELATIONS) out.println("Adding to Mthr: "+bdd1.toStringWithDomains());
        Mthr.orWith(bdd1);        
    }
    
    private void addArrayToAT(ITypeBinding array) {
        // add itself
        TypeWrapper t = new TypeWrapper(array);
        addToAT(t, t);
        
        // add implemented interfaces
        addToAT(CLONEABLE, t);
        addToAT(SERIALIZABLE, t);
        addToAT(OBJECT, t);
        
        // add basetype
        List basetypes = addBindingToAT(array.getElementType());
        int dim = array.getDimensions();
        
        // add [] to returned superclasses of stripped array
        if (dim > 1) {
            // strip []
            String name = array.getQualifiedName();
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
        types.add(CLONEABLE.getBinding().getQualifiedName());
        types.add(SERIALIZABLE.getBinding().getQualifiedName());
        types.add(OBJECT.getBinding().getQualifiedName());   
        
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

    void addToIret(BDD I_bdd, ASTNodeWrapper v) {
        int V_i = Vmap.get(v);
        BDD bdd1 = V1.ithVar(V_i);
        bdd1.andWith(I_bdd.id());
        if (TRACE_RELATIONS) out.println("Adding to Iret: "+bdd1.toStringWithDomains());
        Iret.orWith(bdd1);
    }
    
    
    void addToIthr(BDD I_bdd, ASTNodeWrapper v) {
        int V_i = Vmap.get(v);
        BDD bdd1 = V1.ithVar(V_i);
        bdd1.andWith(I_bdd.id());
        if (TRACE_RELATIONS) out.println("Adding to Ithr: "+bdd1.toStringWithDomains());
        Ithr.orWith(bdd1);
    }
    

    void addToMI(MethodDeclaration m, BDD I_bdd, ASTNodeWrapper target) {
        BDD M_bdd = M.ithVar(Mmap.get(new MethodWrapper(m)));
        int N_i = Nmap.get(target);
        BDD bdd1 = N.ithVar(N_i);
        bdd1.andWith(M_bdd);
        bdd1.andWith(I_bdd.id());
        if (TRACE_RELATIONS) out.println("Adding to mI: "+bdd1.toStringWithDomains());
        mI.orWith(bdd1);
    }
    
    
    void addToIE(ASTNodeWrapper i, IMethodBinding target) {
        int I_i = Imap.get(i);
        BDD I_bdd = I.ithVar(I_i);
        int M2_i = Mmap.get(new MethodWrapper(target));
        BDD bdd1 = M.ithVar(M2_i);
        bdd1.andWith(I_bdd.id());
        if (TRACE_RELATIONS) out.println("Adding to IE: "+bdd1.toStringWithDomains());
        IE.orWith(bdd1);
    }
    
    
}
