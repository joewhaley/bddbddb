/*
 * Created on Jun 24, 2004
 */
package org.sf.bddbddb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;
import java.util.HashMap;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.dom.*;
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.IndexMap;
import org.sf.bddbddb.util.MultiMap;
import org.sf.bddbddb.util.StreamGobbler;
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
    
    static int bddnodes = Integer.parseInt(System.getProperty("bddnodes", "100000"));
    static int bddcache = Integer.parseInt(System.getProperty("bddcache", "10000"));
    static BDDFactory bdd = BDDFactory.init(bddnodes, bddcache);
    
    static BDDDomain V1, V2, I, H1, Z, F, T1, T2, M, N, M2; // H2
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
        M2 = makeDomain("M2", M_BITS);

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
            varorder = "N_F_I_M2_M_Z_V2xV1_T1_T2_H1";
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
        M2set = M2.set();
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
        mL = bdd.zero();
        mS = bdd.zero();
        mIE = bdd.zero();
        mvP = bdd.zero();
        
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
        visited = bdd.zero();
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
        protected ASTNode n; // null for global this or implicit this
        
        ASTNodeWrapper(ASTNode obj) {
            n = obj;
            // peel off parens
            if (obj != null) { 
                n = stripParens(n);
                
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
                s = ((SimpleName)n).resolveBinding().getKey();
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
                    case ASTNode.SUPER_FIELD_ACCESS:  
                    case ASTNode.FIELD_ACCESS:
                    case ASTNode.QUALIFIED_NAME:
                        return false; // might change in future
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
    
    
    class ThisWrapper extends ASTNodeWrapper {
        IMethodBinding enclosingMethod;
                
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
    
    // note unlike other wrappers, this one uses qualified name, not binding key
    class TypeWrapper extends ASTNodeWrapper {
        private ITypeBinding type; // might need to switch to Type in JLS3
        TypeWrapper(ITypeBinding binding) {
            super(null);
            if (binding.isPrimitive()) {
                out.println("ERROR primitive type");
            }
            type = binding;
        }
        
        public String toString() {
            return "TYPE: " + getTypeName();
        }
        
        public boolean equals(Object o) {
            if (o instanceof TypeWrapper) {
                return ((TypeWrapper)o).getTypeName().equals(getTypeName());
            }
            else if (o instanceof StringWrapper) {
                return getTypeName().equals(((StringWrapper)o).name);
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
    
    
    
    // Note: The type of the exception is not the type of the encapsulated ASTNode.
    class ExceptionWrapper extends ASTNodeWrapper {
        ITypeBinding type; // might need to switch to Type in JLS3
        ExceptionWrapper(ASTNode exception, ITypeBinding binding) {
            super(exception);
            type = binding;
        }
        
        public String toString() {
            return "EXCEPTION: " + n + " of type " + type.getQualifiedName();
        }
        
        public boolean equals(Object o) {
            if (o instanceof ExceptionWrapper) {
                ExceptionWrapper ew = (ExceptionWrapper)o;
                if (type.getKey().equals(ew.type.getKey())) {
                    return super.equals(o);
                }
            }
            return false;
        }
        
        public int hashCode() { 
            return n.hashCode();
        }
        
        public ITypeBinding getType() {
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
            return "METHOD: " + method.getKey();
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
        
        public ITypeBinding getType() {
            out.println("ERROR: gettype called on methodwrapper");
            return null;
        }

        public IMethodBinding getBinding() {
            return method;
        }
    }
    
    
    class StringWrapper extends ASTNodeWrapper {
        String name;
        StringWrapper(String s) {
            super(null);
            name = s;
        }
        
        public String toString() {
            return "STRING: " + name;
        }
        
        public boolean equals(Object o) {
            if (o instanceof StringWrapper) {
                return ((StringWrapper)o).name.equals(name);
            }
            else if (o instanceof TypeWrapper) {
                return ((TypeWrapper)o).getTypeName().equals(name);
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

    TypeWrapper CLONEABLE = null;
    TypeWrapper OBJECT = null;
    TypeWrapper SERIALIZABLE = null;
    TypeWrapper STRING = null;
    
    final StringWrapper GLOBAL_THIS = new StringWrapper("GlobalThis"); 
    final StringWrapper ARRAY_FIELD = new StringWrapper("ArrayField");
    final StringWrapper DUMMY_METHOD = new StringWrapper("DummyMethod");
   
    final StringWrapper OUTER_THIS_FIELD = new StringWrapper("OuterThisField");
    
    ASTNode stripParens(ASTNode n) {
        while (n.getNodeType() == ASTNode.PARENTHESIZED_EXPRESSION) {
            n = ((ParenthesizedExpression) n).getExpression();
        }
        return n;
    }
    
    /**
     * @author jzhuang
     */
    class PAASTVisitor extends ASTVisitor {
        
        final boolean libs;
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
        
        /*
        public PAASTVisitor(int i, int s) {
            super(false); // avoid comments
            id = i;
            scope = s;
        }
         */
        public PAASTVisitor(boolean l, boolean r) { 
            super(false); 
            libs = l;
            generateVisited = r;
            /*this(0,0);*/
            
            if (libs) addToMVP(DUMMY_METHOD, GLOBAL_THIS, GLOBAL_THIS);   
            else addToVP(GLOBAL_THIS, GLOBAL_THIS);    
            
            if (generateVisited) addToVisited(DUMMY_METHOD);
        }
        
        // vP
        public boolean visit(ArrayCreation arg0) {
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            if (libs) {
                addToMVP(node, node);
            }
            else addToVP(node, node);
            return true;
        }
        public boolean visit(StringLiteral arg0) {
            ASTNodeWrapper node = new ASTNodeWrapper(arg0);
            if (libs) {
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
            if (libs) {
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
            
            if (libs) {
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
                out.println("bindings unresolved... this shouldn't happen...");
                throw new RuntimeException("unresolved bindings");
            }
            else {
                if (rType.isPrimitive() || rType.isNullType()) return;
                // string +=
                if (arg0.getOperator() == Assignment.Operator.PLUS_ASSIGN) {
                    if (libs) {
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
                        storeToQualifiedField(left, qa.getName(), right);
                    }
                    return;
                case ASTNode.FIELD_ACCESS:
                    FieldAccess fa = (FieldAccess)left;
                    left = fa.getExpression();
                    left.accept(this); // to handle x.y.z = stuff;
                    Name name = fa.getName();
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
                    if (libs) {
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
                    if (libs) {
                        addToMS(GLOBAL_THIS, new ASTNodeWrapper(field), rhs);
                    }
                    else addToS(GLOBAL_THIS, 
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
                            ASTNodeWrapper n = new StringWrapper("ImplicitSuper in " + arg0.resolveBinding().getKey());
                            IMethodBinding[] methods =supClass.getDeclaredMethods(); 
                            IMethodBinding method = null;
                            for (int i = 0; i < methods.length; i++) {
                                if (methods[i].getKey().endsWith("void()")) {
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
                Name f = arg0.getName();  
                if (isStatic(f)) {
                    if (libs) {
                        addToML(GLOBAL_THIS, new ASTNodeWrapper(f), arg0);
                    }
                    else addToL(GLOBAL_THIS, f, arg0);
                }
                else {
                    ThisExpression t = getThis(expr);
                    if (t != null) {
                        addToL(t, f, new ASTNodeWrapper(arg0));
                    }
                    else {
                        if (libs) {
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
                            if (libs) {
                                addToML(GLOBAL_THIS, new ASTNodeWrapper(arg0), 
                                    arg0);
                            }
                            else addToL(GLOBAL_THIS, arg0, arg0);
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
                    if (libs) {
                        addToML(GLOBAL_THIS, 
                            new ASTNodeWrapper(arg0.getName()), arg0);
                    }
                    else addToL(GLOBAL_THIS, arg0.getName(), arg0);
                }
                else { // treat as field
                    ThisExpression t = getThis(arg0.getQualifier());
                    if (t != null) {
                        addToL(t, arg0.getName(), new ASTNodeWrapper(arg0));
                    }
                    else {
                        if (libs) {
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
                if (libs) {
                    addToML(new ASTNodeWrapper(arg0.getArray()), 
                        ARRAY_FIELD, arg0);
                }
                else addToL(new ASTNodeWrapper(arg0.getArray()), 
                        ARRAY_FIELD, new ASTNodeWrapper(arg0));
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
            
            addBindingToAT(classBinding); 
            
            boolean outerthis = hasOuterThis(classBinding);
            IMethodBinding[] bindings = classBinding.getDeclaredMethods();
            for (int i = 0; i < bindings.length; i++) {
                IMethodBinding binding = bindings[i];
                ASTNodeWrapper thisParam;
                if (isStatic(binding)) {
                    thisParam = GLOBAL_THIS;
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
                        OUTER_THIS_FIELD);
                    if (libs) {
                        addToMS(new MethodWrapper(bindings[i]), 
                            thisParam, OUTER_THIS_FIELD, OUTER_THIS_FIELD);
                    }
                    else addToS(thisParam, OUTER_THIS_FIELD, OUTER_THIS_FIELD);
                    
                    addToVT(OUTER_THIS_FIELD, classBinding.getDeclaringClass());
                    
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
            
            if (m instanceof MethodDeclaration) {
                addMThrow((MethodDeclaration)m, arg0.getExpression());
            }
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
            } while (!(n instanceof MethodDeclaration 
                    || n instanceof TryStatement));
            
            if (n instanceof MethodDeclaration) return n;
            
            TryStatement t = (TryStatement)n;
            // n in finally?
            if (prev == t.getFinally()) return findThrowParent(t, ex); 
            
            List catches = t.catchClauses();
            for (Iterator i = catches.iterator(); i.hasNext();) {
                Name var = ((CatchClause)i.next()).getException().getName();

                if (getSuperTypes(ex).contains(var.resolveTypeBinding().getKey())) {
                    return var;// exception caught 
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
                    ITypeBinding sprclass = binding.getSuperclass(); 
                    if (sprclass != null) todo.addLast(sprclass);
                }
            } while (!todo.isEmpty());
            
            return s;
        }
        
        

        private List processStaticInit(Expression qualifier, 
            boolean methodStatic) {
            if (methodStatic) {
                return Collections.singletonList(GLOBAL_THIS);
            }
            else { 
                ThisExpression t = null;
                if (qualifier != null && (t = getThis(qualifier)) == null) {
                    return Collections.singletonList(new ASTNodeWrapper(qualifier));
                }
                else { // implicit this or expr is thisexpr
                   out.println("ERROR: this pter in static initializer");
                   return null;
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
                return Collections.singletonList(GLOBAL_THIS);   
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
                return Collections.singletonList(GLOBAL_THIS); 
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
            ASTNodeWrapper name = stat ? new ASTNodeWrapper(null) :
                    new MethodWrapper(method);       

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
            ASTNodeWrapper name = new StringWrapper(method.getName());
            
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
                ASTNodeWrapper invocation, IMethodBinding invocationBinding, 
                List args, List enclosingMethods, 
                ASTNodeWrapper methodName) {
            int I_i = Imap.get(invocation);
            BDD I_bdd = I.ithVar(I_i);
            ASTNode inv = invocation.getNode();
            if (inv != null) {
                // Mthr, Ithr
                ITypeBinding[] exs = invocationBinding.getExceptionTypes();
                for (int i = 0; i < exs.length; i++) {
                    ExceptionWrapper ew = new ExceptionWrapper(inv, exs[i]);
                    addToIthr(I_bdd, ew); 
                    
                    ASTNode parent = findThrowParent(inv, exs[i]);    
                    if (parent instanceof MethodDeclaration) { 
                        addToMthr((MethodDeclaration)parent, ew); // not caught
                    }
                    else { // caught, match up with var
                        addToA(new ASTNodeWrapper(parent), ew);
                    }
                }
            }
            
            // actual
            for (Iterator i = thisParams.iterator(); i.hasNext(); ) {
                addToActual(I_bdd, 0, (ASTNodeWrapper)i.next());
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
            if (!retType.isPrimitive()) addToIret(I_bdd, invocation);
                   
            // mI
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToMI((ASTNodeWrapper)i.next(), I_bdd, methodName);
            }
            
            // IE
            if (!(methodName instanceof MethodWrapper)) {
                if (libs) {
                    for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                        addToMIE((ASTNodeWrapper)i.next(), I_bdd, invocationBinding);
                    }
                }
                else addToIE(I_bdd, invocationBinding); 
            }
            
            I_bdd.free();
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
            // TODO Auto-generated method stub
            // load
            out.println("ERROR: super field access unhandled");
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
        
        
        void addThisToA(ASTNode v1, ThisExpression e) {
            ASTNode n = findDeclaringParent();
            ASTNodeWrapper v = new ASTNodeWrapper(v1);
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {
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
                n.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {
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
                n.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {
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
            out.println("adding to A " + v1 + " / " + v2); 
            if (TRACE_RELATIONS) out.println("Adding to A: "+bdd1.toStringWithDomains());
            A.orWith(bdd1);
        }
        
        void addToFormal(BDD M_bdd, int z, ASTNodeWrapper v) {
            BDD bdd1 = Z.ithVar(z);
            int V_i = Vmap.get(v);
            bdd1.andWith(V1.ithVar(V_i));
            bdd1.andWith(M_bdd.id());
            out.println("adding to formal " + M_bdd.toStringWithDomains() + " / " + z + " / " + v); 
            if (TRACE_RELATIONS) out.println("Adding to formal: "+bdd1.toStringWithDomains());
            formal.orWith(bdd1);
        }
        
        
        void addToActual(BDD I_bdd, int z, ASTNodeWrapper v) {
            BDD bdd1 = Z.ithVar(z);
            int V_i = Vmap.get(v);
            bdd1.andWith(V2.ithVar(V_i));
            bdd1.andWith(I_bdd.id());
            out.println("adding to actual " + I_bdd.toStringWithDomains() + " / " + z + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to actual: "+bdd1.toStringWithDomains());
            actual.orWith(bdd1);
        }


        void addToMS(ASTNodeWrapper m, ASTNodeWrapper v1,
            ASTNodeWrapper f, ASTNodeWrapper v2) {
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


        
        void addToMS(ASTNodeWrapper q, ASTNodeWrapper f, Expression r) {
            ASTNode decl = findDeclaringParent(); 
            ASTNodeWrapper nw;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION ||
                decl.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {
                Initializer init = getInitializer(r);
                if (init == null) {
                   VariableDeclaration vd = getVarDecl(r);
                   if (isStatic(vd.getName())) {
                       nw = getClinit();   
                   } 
                   else {
                       addToMS(getWrappedConstructors(decl), 
                           q, f, r);
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

        void addToMS(Collection enclosingMethods, ASTNodeWrapper q, 
            ASTNodeWrapper f, Expression v2) {
            ASTNodeWrapper r = new ASTNodeWrapper(v2);
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToMS((ASTNodeWrapper)i.next(), q, f, r);
            }
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
            ASTNode n = findDeclaringParent();
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {
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
                        if (libs) {
                            addToMS(new MethodWrapper(methods[i]), 
                                new ThisWrapper(methods[i], e), 
                                new ASTNodeWrapper(f), v2);
                        }
                        else addToS(new ThisWrapper(methods[i], e), 
                            new ASTNodeWrapper(f), v2);
                    }
                }
            }
            else {// method decl
                if (libs) {
                    addToMS(new MethodWrapper((MethodDeclaration)n), 
                        new ThisWrapper((MethodDeclaration)n, e), 
                        new ASTNodeWrapper(f), v2);
                }
                else addToS(new ThisWrapper((MethodDeclaration)n, e), 
                    new ASTNodeWrapper(f), v2);
            }
        }
        
        void addToS(ASTNodeWrapper v1, ASTNodeWrapper f, 
            ThisExpression e) {
            ASTNode n = findDeclaringParent();
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {
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
                        if (libs) {
                            addToMS(new MethodWrapper(methods[i]), v1, 
                                f, new ThisWrapper(methods[i], e));
                        }
                        else addToS(v1, f, new ThisWrapper(methods[i], e));
                    }
                }
            }
            else {// method decl
                if (libs) {
                    addToMS(new MethodWrapper((MethodDeclaration)n), v1, 
                        f, new ThisWrapper((MethodDeclaration)n, e));
                }
                else addToS(v1, f, new ThisWrapper((MethodDeclaration)n, e));
            }
        }
        
        void addToS(ThisExpression e, ASTNode f, ThisExpression e2) {
            ASTNode n = findDeclaringParent();
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {        
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
                        if (libs) {
                            addToMS(new MethodWrapper(methods[i]), 
                                new ThisWrapper(methods[i], e), 
                                new ASTNodeWrapper(f), 
                                new ThisWrapper(methods[i], e2));
                        
                        }
                        else addToS(new ThisWrapper(methods[i], e), 
                            new ASTNodeWrapper(f), 
                            new ThisWrapper(methods[i], e2));
                    }
                }
            }
            else {
                MethodDeclaration decl = (MethodDeclaration)n;
                if (libs) {
                    addToMS(new MethodWrapper(decl), new ThisWrapper(decl, e), 
                        new ASTNodeWrapper(f), 
                        new ThisWrapper(decl, e2));  
                }
                else addToS(new ThisWrapper(decl, e), new ASTNodeWrapper(f), 
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
            
        void addToML(ASTNodeWrapper m, ASTNodeWrapper v1, 
            ASTNodeWrapper f, ASTNodeWrapper v2) {
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
        
        
        void addToML(ASTNodeWrapper q, ASTNodeWrapper f, Expression r) {
            ASTNode decl = findDeclaringParent(); 
            ASTNodeWrapper nw;
            if (decl.getNodeType() == ASTNode.TYPE_DECLARATION ||
                decl.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
                Initializer init = getInitializer(r);
                if (init == null) {
                   VariableDeclaration vd = getVarDecl(r);
                   if (isStatic(vd.getName())) {
                       nw = getClinit();   
                   } 
                   else {
                       addToML(getWrappedConstructors(decl), 
                           q, f, r);
                       return;
                   }
                }
                else if (isStatic(init)) {
                    nw = getClinit();  
                } 
                else {
                    addToML(getWrappedConstructors(decl), 
                        q, f, r);
                    return;
                }
            }
            else {
                nw = new MethodWrapper((MethodDeclaration)decl);  
            }
            addToML(nw, q, f, new ASTNodeWrapper(r));
        }

        void addToML(Collection enclosingMethods, ASTNodeWrapper q, 
            ASTNodeWrapper f, Expression v2) {
            ASTNodeWrapper r = new ASTNodeWrapper(v2);
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToML((ASTNodeWrapper)i.next(), q, f, r);
            }
        }
        
        void addToL(ASTNodeWrapper v1, ASTNode f, ASTNode v2) {
            if (f == v2) {
                ASTNodeWrapper n = new ASTNodeWrapper(f);
                addToL(v1, n, n);
            }
            else addToL(v1, new ASTNodeWrapper(f), new ASTNodeWrapper(v2));        
        }
            
        void addToL(ThisExpression v1, ASTNode f, ASTNodeWrapper v2) {
            ASTNode n = findDeclaringParent();
            ASTNodeWrapper fw = (v2.getNode() == f) ? v2 : new ASTNodeWrapper(f);
            
            if (n.getNodeType() == ASTNode.TYPE_DECLARATION ||
                n.getNodeType() == ASTNode.ANNOTATION_TYPE_DECLARATION) {
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
                        if (libs) {
                            addToML(new MethodWrapper(methods[i]), 
                                new ThisWrapper(methods[i], v1), fw, v2); 
                        }
                        else addToL(new ThisWrapper(methods[i], v1), fw, v2);   
                    }
                }
            }
            else {// method decl
                if (libs) {
                    addToML(new MethodWrapper((MethodDeclaration)n), 
                        new ThisWrapper((MethodDeclaration)n, v1), fw, v2);
                }
                else addToL(new ThisWrapper((MethodDeclaration)n, v1), fw, v2);
            }
        }
        
        void addToVP(ASTNodeWrapper v, ASTNodeWrapper h) {
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
        
        void addToMVP(ASTNodeWrapper m, ASTNodeWrapper v, 
            ASTNodeWrapper h) {
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
            ASTNodeWrapper nw;
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

        void addToMVP(List enclosingMethods, ASTNodeWrapper v, 
            ASTNodeWrapper h) {
            for (Iterator i = enclosingMethods.iterator(); i.hasNext(); ) {
                addToMVP((ASTNodeWrapper)i.next(), v, h);
            }
        }

        private void addToMret(MethodDeclaration m, ASTNodeWrapper v) {
            int V_i = Vmap.get(v);
            int M_i = Mmap.get(new MethodWrapper(m));
            BDD M_bdd = M.ithVar(M_i);
            BDD bdd1 = V2.ithVar(V_i);
            bdd1.andWith(M_bdd);
            out.println("Adding to Mret: "+ new MethodWrapper(m) + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to Mret: "+bdd1.toStringWithDomains());
            Mret.orWith(bdd1);
            
        }
            
        private void addToMthr(MethodDeclaration m, ASTNodeWrapper v) {
            int V_i = Vmap.get(v);
            int M_i = Mmap.get(new MethodWrapper(m));
            BDD M_bdd = M.ithVar(M_i);
            BDD bdd1 = V2.ithVar(V_i);
            bdd1.andWith(M_bdd);
            out.println("Adding to Mthr: "+ new MethodWrapper(m) + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to Mthr: "+bdd1.toStringWithDomains());
            Mthr.orWith(bdd1);        
        }
        

        void addToIret(BDD I_bdd, ASTNodeWrapper v) {
            int V_i = Vmap.get(v);
            BDD bdd1 = V1.ithVar(V_i);
            bdd1.andWith(I_bdd.id());
            out.println("Adding to Iret: "+ I_bdd.toStringWithDomains() + " / " + v);
            if (TRACE_RELATIONS) out.println("Adding to Iret: "+bdd1.toStringWithDomains());
            Iret.orWith(bdd1);
        }
        
        
        void addToIthr(BDD I_bdd, ASTNodeWrapper v) {
            int V_i = Vmap.get(v);
            BDD bdd1 = V1.ithVar(V_i);
            bdd1.andWith(I_bdd.id());
            out.println("Adding to Ithr: "+ I_bdd.toStringWithDomains() + " / " + v);       
            if (TRACE_RELATIONS) out.println("Adding to Ithr: "+bdd1.toStringWithDomains());
            Ithr.orWith(bdd1);
        }
        
        

        void addToMI(ASTNodeWrapper m, BDD I_bdd, ASTNodeWrapper target) {
            BDD M_bdd = M.ithVar(Mmap.get(m));
            int N_i = Nmap.get(target);
            BDD bdd1 = N.ithVar(N_i);
            bdd1.andWith(M_bdd);
            bdd1.andWith(I_bdd.id());
            out.println("Adding to mI: "+ m+ " / " +I_bdd.toStringWithDomains() + " / " + target); 
            if (TRACE_RELATIONS) out.println("Adding to mI: "+bdd1.toStringWithDomains());
            mI.orWith(bdd1);
        }
           
        void addToIE(BDD I_bdd, IMethodBinding target) {            
            int M2_i = Mmap.get(new MethodWrapper(target));
            BDD bdd1 = M.ithVar(M2_i);
            bdd1.andWith(I_bdd.id());
            out.println("Adding to IE: "+ I_bdd.toStringWithDomains()+ 
                " / " +new MethodWrapper(target) ); 
            if (TRACE_RELATIONS) out.println("Adding to IE: "+bdd1.toStringWithDomains());
            IE.orWith(bdd1);
        }
        

        void addToMIE(ASTNodeWrapper m, BDD I_bdd, IMethodBinding target) {
            int M_i = Mmap.get(m);
            BDD M_bdd = M.ithVar(M_i);
            int M2_i = Mmap.get(new MethodWrapper(target));
            BDD bdd1 = M2.ithVar(M2_i);
            bdd1.andWith(I_bdd.id());
            bdd1.andWith(M_bdd);
            if (TRACE_RELATIONS) out.println("Adding to mIE: "+bdd1.toStringWithDomains());
            mIE.orWith(bdd1);
        }
        
        void addToVisited(ASTNodeWrapper m) {
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
                out.println("ERROR empty decl stack");
                return null;
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
    
    private boolean isField(Name n) {
        IBinding bind = n.resolveBinding();
        if (bind.getKind() == IBinding.VARIABLE) {
            return ((IVariableBinding)bind).isField();
        }
        return false;
    }
    

    Initializer getInitializer(ASTNode n) {
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
    
    private boolean isStatic(Name n) {
        return Modifier.isStatic(n.resolveBinding().getModifiers());
    }
    
    private boolean isStatic(BodyDeclaration n) {
        return Modifier.isStatic(n.getModifiers());
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
     
        dis.run(files, Collections.EMPTY_SET);
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
     * @param dotJava
     * @param dotClass
     * @throws IOException
     */
    public void run(Set dotJava, Set dotClass) throws IOException {
        System.out.println(dotJava.size() + " .java files to parse.");
        System.out.println(dotClass.size() + " .class files to parse.");
        if (dotJava.size() == 0 && dotClass.size() == 0) return;
        
        resetBDDs();
        initializeMaps();

        // Start timing.
        long time = System.currentTimeMillis();
        
        out.println("Processing .java files");
        //generateASTs(dotJava);
        //while (!todo.isEmpty()) {
        //    generateRelations(true, true);
        //}
        for (Iterator i = dotJava.iterator(); i.hasNext(); ) {
            Object o = i.next();
            parseAST(o);
            generateRelations(true, true);
        }
        
        
        out.println("Processing .class files");
        //generateASTs(dotClass);
//        while (!todo.isEmpty()) {
//            generateRelations(true, false);
//        }
        for (Iterator i = dotClass.iterator(); i.hasNext(); ) {
            Object o = i.next();
            parseAST(o);
            generateRelations(true, true);
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
        
        // hT
        it = Hmap.iterator();
        for (int i = 0; it.hasNext(); i++) {
            ASTNodeWrapper h =(ASTNodeWrapper)it.next();
            addToHT(i, h);
        }
    
        // TODO transitive closure on aT
        
        System.out.println("Time spent : "+(System.currentTimeMillis()-time)/1000.);
               
        System.out.println("Writing relations...");
        time = System.currentTimeMillis();
        dumpBDDRelations();
        System.out.println("Time spent writing: "+(System.currentTimeMillis()-time)/1000.);

        out.println("Calling bddbddb...");
        callBddBddb();
    }

    
    private void callBddBddb() {
        String dumpPath = System.getProperty("pas.dumppath", "");
        if (dumpPath.length() > 0) {
            String sep = System.getProperty("file.separator", "/");
            if (!dumpPath.endsWith(sep))
                dumpPath += sep;
        }
        //File f = new File("c:\\runtime-workspace\\joeq_test\\");
        String path = dumpPath + "pafly.datalog"; 
        String bddbddb = dumpPath + "bddbddb.jar";
        
        String[] cmd = new String[] {"java", "-jar", bddbddb, path }; 

        int r = -1;
        try {
            Process p = Runtime.getRuntime().exec(cmd);
            StreamGobbler output = new StreamGobbler(p.getInputStream(), "bddbddb OUT");
            StreamGobbler error = new StreamGobbler(p.getErrorStream(), "bddbddb ERR", System.err);

            output.start();
            error.start();
            
            r = p.waitFor(); 
            
            out.println("dumping callgraph...");
            MultiMap mm = parseIETuples(dumpPath + "IE.rtuples");
            
            writeCallgraph(dumpPath + "callgraph", mm);
            out.println("callgraph dumped.");
        } catch (Exception e) {
            e.printStackTrace();
        }
        if (r != 0) {
            out.println("bddbddb failed: " + r);
            return;
        }
    }
    

    private void writeCallgraph(String file, MultiMap mm) throws IOException {
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
                writer.write(" METHOD: <clinit> ()V ROOT\n");
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
                    String s = "ImplicitSuper in " + mb[i].getKey();
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

    private void writeCallsite(BufferedWriter writer, Collection targets, ASTNodeWrapper w) throws IOException {
        writer.write("  CALLSITE ");
        writer.write(String.valueOf(Imap.get(w)));
        writer.write('\n');
        
        for (Iterator j = targets.iterator(); j.hasNext(); ) {   
            writeTarget(writer, (MethodWrapper)j.next());
        }
    }
    
    
    boolean isInVisited(IMethodBinding binding) {
        String k = binding.getKey();
        return (isStatic(binding) && k.indexOf("voidmain(java/lang/String1)") != -1) 
                    || (k.indexOf("voidfinalize()") != -1) 
                    || (k.indexOf("voidrun()") != -1);
    }

    private void writeMethod(BufferedWriter writer, IMethodBinding mb) throws IOException {
        writer.write(" METHOD: ");
        writer.write(getFormattedName(mb));
        if (isInVisited(mb)) {
            writer.write(" ROOT");
        }
        writer.write("\n");
    }

    private void writeTarget(BufferedWriter writer, MethodWrapper mw) throws IOException {
        writer.write("   TARGET ");
        IMethodBinding binding = mw.getBinding();
        writer.write(binding.getDeclaringClass().getKey());
        writer.write('.');
        writer.write(getFormattedName(binding));
        writer.write('\n');
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
    
    
    private MultiMap parseIETuples(String file) throws IOException {
        BufferedReader in = new BufferedReader(new FileReader(file));
        MultiMap mm = new GenericMultiMap();
        String line;
        while ((line = in.readLine()) != null) {
            if (line.startsWith("#")) continue;
                
            String[] tuple = line.split("\\s"); // (I, M)
            
            Object i;
            ASTNodeWrapper wrapper = (ASTNodeWrapper)Imap.get(Integer.parseInt(tuple[0]));
            if (wrapper instanceof StringWrapper) {
                i = ((StringWrapper)wrapper).getString();
            }
            else {
                i = wrapper.getNode();
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
  
    public void dumpBDDRelations() throws IOException {     
        cha = new ClassHierarchyAnalysis(this).calculateCHA();
        
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
                else if (d == N)
                    dos.writeBytes("N\n");
                else if (d == M || d == M2)
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
            dos.writeBytes("N "+(1L<<N_BITS)+" name.map\n");
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
        
        dos = null;
        try {
            dos = new DataOutputStream(new FileOutputStream(dumpPath+"name.map"));
            Nmap.dumpStrings(dos);
        } finally {
            if (dos != null) dos.close();
        }
        
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
        Hmap.get(GLOBAL_THIS);
        Fmap = makeMap("Fields", F_BITS);
        Tmap = makeMap("Types", T_BITS);
        Tmap.get(GLOBAL_THIS);
        Nmap = makeMap("Names", N_BITS);
        Mmap = makeMap("Methods", M_BITS);
        Mmap.get(DUMMY_METHOD); 
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
    
    
    private void parseAST(Object file) {
        CompilationUnit cu;
        try {
            if (file instanceof String) {
                cu = readSourceFile((String) file);
            } else {
                ASTParser c = ASTParser.newParser(AST.JLS2);
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
                
                todo.add(cu);
            }                
        }
        catch (IllegalStateException e) {
            if (!(file instanceof IClassFile)) {// otherwise ignore
                e.printStackTrace();
            }
        }
    }

    private void generateRelations(boolean libs, boolean root) {
        CompilationUnit cu = (CompilationUnit)todo.remove(todo.size()-1);

        //cu.accept(new ConstructorVisitor());
        cu.accept(new PAASTVisitor(libs, root));  

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

    void addToVT(StringWrapper v, ITypeBinding type) {
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
      
    void addToVT(int V_i, ASTNodeWrapper v) {
        if (v instanceof TypeWrapper || v instanceof MethodWrapper) {
            out.println("ERROR: this type of node shouldn't be in V: " + v);
            return;
        }
        
        ITypeBinding type = v.getType();
        if (type == null) {
            if (v instanceof StringWrapper) {
                if (v == GLOBAL_THIS) {
                    BDD bdd1 = V1.ithVar(V_i);
                    bdd1.andWith(T1.ithVar(0));
                    out.println("adding to vT: 0 / " + GLOBAL_THIS);
                    if (TRACE_RELATIONS) out.println("Adding to vT: "+bdd1.toStringWithDomains());
                    vT.orWith(bdd1);
                }
                else if (v == OUTER_THIS_FIELD) {
                    // vT added added when OUTER_THIS_FIELD is added to Vmap
                    return;
                }
                else out.println("ERROR: unhandled stringwrapper node in V: " + v);
            }
            else out.println("ERROR: gettype returned null");
        }
        else {
            BDD bdd1 = V1.ithVar(V_i);
            TypeWrapper tw = new TypeWrapper(type);
            int T_i = Tmap.get(tw);
            bdd1.andWith(T1.ithVar(T_i));
            out.println("adding to vT: " + V_i + " " + v+  " / " +
                tw.getTypeName());
            if (TRACE_RELATIONS) out.println("Adding to vT: "+bdd1.toStringWithDomains());
            vT.orWith(bdd1);
        }
    }
    
    void addToHT(int H_i, ASTNodeWrapper h) {
        if (h instanceof ThisWrapper || h instanceof MethodWrapper ||
            h instanceof StringWrapper || 
            h instanceof TypeWrapper) {
            out.println("ERROR: this type of node shouldn't be in H");
        }
        else {
            ITypeBinding type = h.getType();
            if (type == null) {
                out.println("ERROR: this type of node shouldn't be in H");
            }
            TypeWrapper tw = new TypeWrapper(type);
            int T_i = Tmap.get(tw);
            BDD T_bdd = T2.ithVar(T_i);
            BDD bdd1 = H1.ithVar(H_i);
            bdd1.andWith(T_bdd);
            out.println("adding to hT: " + H_i + " " + h+ 
                " / " + tw.getTypeName());
            if (TRACE_RELATIONS) out.println("Adding to hT: "+bdd1.toStringWithDomains());
            hT.orWith(bdd1);
        }        
    }
    
    // supertype, subtype
    void addToAT(ASTNodeWrapper t1, ASTNodeWrapper t2) {
        int T1_i = Tmap.get(t1);
        int T2_i = Tmap.get(t2);
        BDD T1_bdd = T1.ithVar(T1_i);
        BDD bdd1 = T2.ithVar(T2_i);
        bdd1.andWith(T1_bdd);
        out.println("Adding to aT: "+ T1_i + " " + t1+" / " + T2_i + " " + t2);
        if (TRACE_RELATIONS) out.println("Adding to aT: "+bdd1.toStringWithDomains());
        aT.orWith(bdd1);
    }
    
    private List addBindingToAT(ITypeBinding binding) {
        List types = new LinkedList();
        TypeWrapper tw = new TypeWrapper(binding);
        types.add(tw.getTypeName());
        if (binding.isPrimitive()) return types;
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


    private void addArrayToAT(ASTNodeWrapper w) {
        Expression e = (Expression) w.getNode();
        if (e == null) return;
        ITypeBinding t = e.resolveTypeBinding();
        if (t.isArray()) addArrayToAT(t);
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

    
    List/*IMethodBinding*/ getConstructors(ASTNode n) {
        ArrayList l = new ArrayList();
        
        ITypeBinding p;
        if (n.getNodeType() == ASTNode.TYPE_DECLARATION) {
            p = ((TypeDeclaration)n).resolveBinding();
        }
        else if (n.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
            p = ((AnonymousClassDeclaration)n).resolveBinding();
        }
        else {
            out.println("ERROR unsupported type");
            return null;
        }
        
        IMethodBinding[] methods = p.getDeclaredMethods();
        for (int i = 0; i < methods.length; i++) {
            if (methods[i].isConstructor()) {
               l.add(methods[i]);
            }
        }
        return l;
    }
    
    List/*MethodWrapper*/ getWrappedConstructors(ASTNode n) {
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
    
    boolean hasOuterThis(ITypeBinding binding) {
        // TODO need isclass check?
        return binding.isNested() && binding.isClass() && !isStatic(binding);
    }
}
