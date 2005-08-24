// PAFly.java, created Mar 15, 2005 1:08:07 AM 2005 by jwhaley
// Copyright (C) 2005 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.math.BigInteger;
import joeq.Class.PrimordialClassLoader;
import joeq.Class.jq_Class;
import joeq.Class.jq_FakeInstanceMethod;
import joeq.Class.jq_Field;
import joeq.Class.jq_Initializer;
import joeq.Class.jq_Member;
import joeq.Class.jq_Method;
import joeq.Class.jq_NameAndDesc;
import joeq.Class.jq_Reference;
import joeq.Class.jq_Type;
import joeq.Class.jq_Reference.jq_NullType;
import joeq.Compiler.Analysis.FlowInsensitive.MethodSummary;
import joeq.Compiler.Analysis.FlowInsensitive.ReflectionInformationProvider;
import joeq.Compiler.Analysis.FlowInsensitive.MethodSummary.CheckCastNode;
import joeq.Compiler.Analysis.FlowInsensitive.MethodSummary.ConcreteObjectNode;
import joeq.Compiler.Analysis.FlowInsensitive.MethodSummary.ConcreteTypeNode;
import joeq.Compiler.Analysis.FlowInsensitive.MethodSummary.GlobalNode;
import joeq.Compiler.Analysis.FlowInsensitive.MethodSummary.Node;
import joeq.Compiler.Analysis.FlowInsensitive.MethodSummary.UnknownTypeNode;
import joeq.Compiler.Analysis.IPA.PA;
import joeq.Compiler.Analysis.IPA.ProgramLocation;
import joeq.Compiler.Analysis.IPA.PACallGraph.BDDSet;
import joeq.Compiler.Quad.CachedCallGraph;
import joeq.Compiler.Quad.CallGraph;
import joeq.Compiler.Quad.CodeCache;
import joeq.Compiler.Quad.LoadedCallGraph;
import joeq.Compiler.Quad.Operand;
import joeq.Compiler.Quad.Operator;
import joeq.Compiler.Quad.Quad;
import joeq.Main.HostedVM;
import joeq.UTF.Utf8;
import jwutil.collections.Filter;
import jwutil.collections.FilterIterator;
import jwutil.collections.IndexMap;
import jwutil.collections.IndexedMap;
import jwutil.collections.Pair;
import jwutil.util.Assert;
import net.sf.bddbddb.Attribute;
import net.sf.bddbddb.BDDRelation;
import net.sf.bddbddb.BDDSolver;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDD.BDDIterator;

/**
 * PAFly
 * 
 * @author jwhaley
 * @version $Id$
 */
public class PAFly {
    static BDD prev;
    
    static boolean initialized = false;

    private static OfflineSubtypeHelper subtypeHelper;
    
    static {
        HostedVM.initialize();
        CodeCache.AlwaysMap = true;
    }
    
    static void initialize(BDDSolver s) {
        if (initialized) {
            return;
        }
        
        initialized = true;
        
        Field[] f = PAFly.class.getDeclaredFields();
        for (int i = 0; i < f.length; ++i) {
            if (f[i].getType() != BDDRelation.class) continue;
            BDDRelation r = (BDDRelation) s.getRelation(f[i].getName());
            try {
                f[i].set(null, r);
            } catch (IllegalArgumentException e) {
                e.printStackTrace();
            } catch (IllegalAccessException e) {
                e.printStackTrace();
            }
        }
        Vmap = s.getDomain("V").getMap(); if (Vmap == null) Vmap = new IndexMap("var");
        Fmap = s.getDomain("F").getMap(); if (Fmap == null) Fmap = new IndexMap("field");
        Hmap = s.getDomain("H").getMap(); if (Hmap == null) Hmap = new IndexMap("heap");
        Mmap = s.getDomain("M").getMap(); if (Mmap == null) Mmap = new IndexMap("method");
        Imap = s.getDomain("I").getMap(); if (Imap == null) Imap = new IndexMap("invoke");
        Tmap = s.getDomain("T").getMap(); if (Tmap == null) Tmap = new IndexMap("type");
        Nmap = s.getDomain("N").getMap(); if (Nmap == null) Nmap = new IndexMap("name");
        
        if (subtypes != null) {
            subtypeHelper = new OfflineSubtypeHelper();
            for (Iterator i = subtypeHelper.allClasses().iterator(); i.hasNext(); ) {
                String className = (String) i.next();
                String cn = canonicalizeClassName(className.trim());
                jq_Type t1 = jq_Type.parseType(cn);
                if (t1 instanceof jq_Class) {
                    Collection st = subtypeHelper.getSubtypes((jq_Class) t1);
                    if (st == null){
                        System.err.println("No subtypes for class " + t1.getName());
                        continue;
                    }
                    int T1_i = Tmap.get(t1.toString());
                    for (Iterator typeIter = st.iterator(); typeIter.hasNext();){
                        jq_Class t2 = (jq_Class) typeIter.next();
                        int T2_i = Tmap.get(t2.toString());
                        if (TRACE_RELATIONS) out.println("Adding to subtypes: "+T1_i+","+T2_i);
                        subtypes.add(T1_i, T2_i);
                    }
                }
            }
        }
        
        for (Iterator i = Tmap.iterator(); i.hasNext(); ) {
            String st = (String) i.next();
            jq_Reference t;
            if (st.equals("null") || st.equals("NULL_TYPE")) t = null;
            else t = (jq_Reference) jq_Type.parseType(st);
            visitType(t);
        }
        
        // Add the default static variables (System in/out/err...)
        GlobalNode.GLOBAL.addDefaultStatics();
        
    }
    
    static String canonicalizeClassName(String s) {
        if (s.endsWith(".class")) s = s.substring(0, s.length() - 6);
        s = s.replace('.', '/');
        String desc = "L" + s + ";";
        return desc;
    }
    
    public static class OfflineSubtypeHelper {
        static final String subtypeFileName = "reversed_subclasses.txt";
        Map classes2subclasses = new HashMap();
        Set allClasses = new HashSet();
        private boolean initialized = false;
        //final static String kind = OFFLINE;
        public OfflineSubtypeHelper() {
        }
        
        Set allClasses() {
            return allClasses;
        }
        
        void initializeSubclasses() throws IOException {
            if(initialized) return;
            BufferedReader r = new BufferedReader(new FileReader(subtypeFileName));
            String s = null;
            String className = null;
            Collection subclassList = null;
            while ((s = r.readLine()) != null) {
                if(s.startsWith("CLASS ")){                    
                    className = s.substring("CLASS ".length(), s.indexOf(" ", "CLASS ".length() + 1));
                    subclassList = new LinkedList();
                    // add the class itself to the list of subclasses
                    subclassList.add(className);
                    classes2subclasses.put(className, subclassList);
                    allClasses.add(className);
                }else{
                    int index = s.indexOf("SUBCLASS ");
                    if(index != -1){
                        String subclass = s.substring(index + "SUBCLASS ".length(), s.length());
                        subclassList.add(subclass);
                        allClasses.add(subclass);
                    }
                }
            }
            initialized = true;
        }

        /* (non-Javadoc)
         * @see joeq.Compiler.Analysis.IPA.SubtypeHelper#getSubtypes(joeq.Class.jq_Class)
         */
        public Collection getSubtypes(jq_Class clazz) {
            if(TRACE) System.out.println("Requesting subtypes of class " + clazz);
            String className = clazz.getName();
            try {
                initializeSubclasses();         // lazily initialize the subclasses
            } catch (IOException e) {
                Assert._assert(false, e.toString());
                return null;
            }
            
            Collection subtypeNames = (Collection) classes2subclasses.get(className);
            if(subtypeNames == null){
                System.err.println("No match for class \"" + className + "\" in " + subtypeFileName);
                return null;
            }
            Collection result = new LinkedList();
            for(Iterator iter = subtypeNames.iterator(); iter.hasNext();){
                String subtypeName = (String) iter.next();
                String canonicalName = canonicalizeClassName(subtypeName.trim());
                
                try {
                    jq_Class subtypeClass = (jq_Class) jq_Class.parseType(canonicalName);
                    subtypeClass.prepare();
                    result.add(subtypeClass);
                } catch (java.lang.NoClassDefFoundError e){
                    if(TRACE) System.err.println("Can't load " + subtypeName + ": " + e);
                    continue;
                }
            }
            Assert._assert(result.size() <= subtypeNames.size());
            
            if(TRACE) System.out.println("Returning " + result.size() + " subtypes.");
            return result;
        }
    }
    
    static void saveAll(BDDSolver s) throws IOException {
        if (!new File(s.getBaseDir()).exists()) {
            new File(s.getBaseDir()).mkdirs();
        }
        Field[] f = PAFly.class.getDeclaredFields();
        for (int i = 0; i < f.length; ++i) {
            if (f[i].getType() != BDDRelation.class) continue;
            BDDRelation r = (BDDRelation) s.getRelation(f[i].getName());
            if (r != null) r.save();
        }
        saveMaps(s);
    }
    
    static void saveMaps(BDDSolver s) throws IOException {
        System.out.print("Saving maps...");
        BufferedWriter w = new BufferedWriter(new FileWriter(s.getBaseDir()+"var.map"));
        Vmap.dumpStrings(w);
        w.close();
        w = new BufferedWriter(new FileWriter(s.getBaseDir()+"field.map"));
        Fmap.dumpStrings(w);
        w.close();
        w = new BufferedWriter(new FileWriter(s.getBaseDir()+"heap.map"));
        Hmap.dumpStrings(w);
        w.close();
        w = new BufferedWriter(new FileWriter(s.getBaseDir()+"method.map"));
        Mmap.dumpStrings(w);
        w.close();
        w = new BufferedWriter(new FileWriter(s.getBaseDir()+"invoke.map"));
        Imap.dumpStrings(w);
        w.close();
        w = new BufferedWriter(new FileWriter(s.getBaseDir()+"type.map"));
        Tmap.dumpStrings(w);
        w.close();
        w = new BufferedWriter(new FileWriter(s.getBaseDir()+"name.map"));
        Nmap.dumpStrings(w);
        w.close();
        w = new BufferedWriter(new FileWriter(s.getBaseDir()+"fielddomains.pa"));
        w.write("V "+s.getDomain("V").getSize()+" var.map\n");
        w.write("H "+s.getDomain("H").getSize()+" heap.map\n");
        w.write("T "+s.getDomain("T").getSize()+" type.map\n");
        w.write("F "+s.getDomain("F").getSize()+" field.map\n");
        w.write("I "+s.getDomain("I").getSize()+" invoke.map\n");
        w.write("Z "+s.getDomain("Z").getSize()+"\n");
        w.write("N "+s.getDomain("N").getSize()+" name.map\n");
        w.write("M "+s.getDomain("M").getSize()+" method.map\n");
        w.close();
        System.out.println("done.");
    }
    
    public static void addToReachable(BDDRelation r) {
        BDD newValues;
        if (prev == null) {
            newValues = r.getBDD().id();
            final BDDSolver s = r.getSolver();
            initialize(s);
            s.addSaveHook(new Runnable() {
                public void run() {
                    try {
                        saveMaps(s);
                        dumpCallGraph(s.getBaseDir()+"callgraph");
                    } catch (IOException x) {
                        x.printStackTrace();
                    }
                }
            });
        } else {
            newValues = r.getBDD().apply(prev, BDDFactory.diff);
            prev.free();
        }
        if (TRACE) System.out.println("Relation "+r+" new values: "+newValues.satCount(r.getDomainSet()));
        Attribute a = r.getAttribute("method");
        BDDDomain M = r.getBDDDomain(a);
        List newMethods = new LinkedList();
        for (BDDIterator i = newValues.iterator(r.getDomainSet()); i.hasNext(); ) {
            BDD b = (BDD) i.next();
            BigInteger M_i = b.scanVar(M);
            String methodName = a.getDomain().toString(M_i);
            if(TRACE) System.out.println("NEW REACHABLE METHOD: "+methodName);
            jq_Method m = (jq_Method) jq_Member.parseMember(methodName);
            if (m != null) {
                // Don't call visitMethod here, as it may increase domain sizes
                // which will screw up our iterator.  Instead, we add it to a list
                // for later processing.
                newMethods.add(m);
            } else {
                System.out.println("Warning: Cannot find "+methodName);
            }
            b.free();
        }
        newValues.free();
        for (Iterator i = newMethods.iterator(); i.hasNext(); ) {
            jq_Method m = (jq_Method) i.next();
            visitMethod(m);
        }
        prev = r.getBDD().id();
    }
    
    static BDD prevH;
    public static void addToHDomain(BDDRelation r) {
        initialize(r.getSolver());
        
        BDD newValues;
        if (prevH == null) {
            newValues = r.getBDD().id();
        } else {
            newValues = r.getBDD().apply(prevH, BDDFactory.diff);
            prevH.free();
        }
        Attribute a = r.getAttribute("i");
        BDDDomain I = r.getBDDDomain(a);
        List invokes = new LinkedList();
        for (BDDIterator i = newValues.iterator(r.getDomainSet()); i.hasNext(); ) {
            BDD b = (BDD) i.next();
            BigInteger I_i = b.scanVar(I);
            b.free();
            // Don't add to mapIH here, as it may increase domain sizes
            // which will screw up our iterator.  Instead, we add it to a list
            // for later processing.
            invokes.add(I_i);
        }
        for (Iterator i = invokes.iterator(); i.hasNext(); ) {
            BigInteger I_i = (BigInteger) i.next();
            String invokeName = a.getDomain().toString(I_i);
            if (TRACE) System.out.println("NEW INVOKE TO ADD TO HEAP: "+invokeName);
            int H_i = Hmap.get(invokeName);
            if (TRACE) out.println("Adding to mapIH: "+I_i+","+H_i);
            mapIH.add(I_i.intValue(), H_i);
        }
        newValues.free();
        prevH = r.getBDD().id();
    }
    
    /*
     * <h, m, i>
     * */
    public static void addNewHToHDomain(BDDRelation r) {
        BDD newValues;
        if (prevH == null) {
            newValues = r.getBDD().id();
        } else {
            newValues = r.getBDD().apply(prevH, BDDFactory.diff);
            prevH.free();
        }
        Attribute a = r.getAttribute("i");
        BDDDomain I = r.getBDDDomain(a);
        List heaps = new LinkedList();
        for (BDDIterator i = newValues.iterator(r.getDomainSet()); i.hasNext(); ) {
            BDD b = (BDD) i.next();
            BigInteger I_i = b.scanVar(I);
            b.free();
            // Don't add to mapIH here, as it may increase domain sizes
            // which will screw up our iterator.  Instead, we add it to a list
            // for later processing.
            heaps.add(I_i);
        }
        for (Iterator i = heaps.iterator(); i.hasNext(); ) {
            BigInteger I_i = (BigInteger) i.next();
            String heapName = "clone of " + a.getDomain().toString(I_i);
            if (TRACE) System.out.println("NEW ALLOC TO ADD TO HEAP: "+heapName);
            int H_i = Hmap.get(heapName);
            if (TRACE) out.println("Adding to mapIH: "+I_i+","+H_i);
            mapIH.add(I_i.intValue(), H_i);
        }
        newValues.free();
        prevH = r.getBDD().id();
    }
    
    static BDD prevC;
    public static void addToClassObjectType(BDDRelation r) {
        initialize(r.getSolver());
        
        Attribute a = r.getAttribute("heap");
        BDDDomain H = r.getBDDDomain(a);
        BDD Hset = H.set();
        BDD newValues;
        if (prevC == null) {
            newValues = r.getBDD().exist(Hset);
        } else {
            newValues = r.getBDD().exist(Hset);
            newValues.applyWith(prevC, BDDFactory.diff);
        }
        a = r.getAttribute("type");
        BDDDomain T = r.getBDDDomain(a);
        BDD Tset = T.set();
        List types = new LinkedList();
        for (BDDIterator i = newValues.iterator(Tset); i.hasNext(); ) {
            BDD b = (BDD) i.next();
            BigInteger T_i = b.scanVar(T);
            b.free();
            String T_s = a.getDomain().toString(T_i);
            if (TRACE) System.out.println("NEW CLASS OBJECT: "+T_s);
            if (T_s != null && !T_s.equals("null") && !T_s.equals("NULL_TYPE")) {
                jq_Reference t = (jq_Reference) jq_Type.parseType(T_s);
                // Don't call addClassInitializer here, as it may increase domain sizes
                // which will screw up our iterator.  Instead, we add it to a list
                // for later processing.
                types.add(t);
            }
        }
        Tset.free();
        for (Iterator i = types.iterator(); i.hasNext(); ) {
            jq_Reference t = (jq_Reference) i.next();
            if (t instanceof jq_Class) {
                jq_Class c = (jq_Class) t;
                addClassInitializer(c);
            }
        }
        prevC = r.getBDD().exist(Hset);
        Hset.free();
    }
    
    public static PrintStream out = System.out;
    public static boolean TRACE = !System.getProperty("pa.trace", "no").equals("no");
    public static boolean TRACE_RELATIONS = !System.getProperty("pa.tracerelations", "no").equals("no");
    public static boolean USE_BOGUS_SUMMARIES = !System.getProperty("pa.usebogussummaries", "no").equals("no");
    public static boolean FILTER_NULL = !System.getProperty("pa.filternull", "yes").equals("no");
    public static boolean USE_REFLECTION_PROVIDER = !System.getProperty("pa.usereflectionprovider", "no").equals("no");
    public static boolean RESOLVE_REFLECTION = !System.getProperty("pa.resolvereflection", "no").equals("no");
    public static boolean USE_CASTS_FOR_REFLECTION = !System.getProperty("pa.usecastsforreflection", "no").equals("no");
    public static boolean RESOLVE_FORNAME = !System.getProperty("pa.resolveforname", "no").equals("no");
    
    static BDDRelation vP0, L, S, A, actual, formal, Mret, Iret, Mthr, /*mV, */ Ithr, IE0, vT, hT, aT, cha, mI, roots, IE;
    static BDDRelation stringToType, stringToField, stringToMethod, defaultConstructor, allConstructors, mapIH, skipMethod;
    static BDDRelation subtypes;
    static IndexMap Vmap, Fmap, Hmap, Mmap, Imap, Tmap, Nmap;
    static Collection stringNodes = new LinkedList();
    
    static void addToVP0(int V_i, Node h) {
        if (FILTER_NULL && isNullConstant(h))
            return;
        int oldSize = Hmap.size();
        int H_i = Hmap.get(h.toString());
        if (H_i >= oldSize) {
            addToHT(H_i, h.getDeclaredType());
            String s = (String) MethodSummary.stringNodes2Values.get(h);
            if (s != null) {
                stringNodes.add(h);
                if (TRACE) out.println("String Node: "+h+" = \""+s+"\"");
                jq_Class t = tryLoadingClass(s);
                if (t != null) {
                    int T_i = Tmap.get(t.toString());
                    if (true) out.println("Adding to stringToType: "+H_i+","+T_i+" "+t);
                    stringToType.add(H_i, T_i);
                }
                for (int i = 0; i < Tmap.size(); ++i) {
                    String T1_s = (String) Tmap.get(i);
                    jq_Reference t1 = null;
                    if (T1_s != null && !T1_s.equals("null") && !T1_s.equals("NULL_TYPE"))
                        t1 = (jq_Reference) jq_Type.parseType(T1_s);
                    if (t1 instanceof jq_Class) {
                        jq_Class c = (jq_Class) t1;
                        handleString(H_i, s, c);
                    }
                }
            }
        }
        if (TRACE_RELATIONS) out.println("Adding to vP0: "+V_i+","+H_i);
        vP0.add(V_i, H_i);
    }
    
    static void handleString(int H_i, String s, jq_Class c) {
        jq_Field f = c.getDeclaredField(s);
        if (f != null) {
            int F_i = Fmap.get(f.toString());
            if (TRACE_RELATIONS) out.println("Adding to stringToField: "+H_i+","+F_i);
            stringToField.add(H_i, F_i);
        }
        jq_Method[] m = c.getDeclaredInstanceMethods();
        for (int j = 0; j < m.length; ++j) {
            if (m[j].getName().toString().equals(s)) {
                int M_i = Mmap.get(m[j].toString());
                if (TRACE_RELATIONS) out.println("Adding to stringToMethod: "+H_i+","+M_i);
                stringToMethod.add(H_i, M_i);
            }
        }
        m = c.getDeclaredStaticMethods();
        for (int j = 0; j < m.length; ++j) {
            if (m[j].getName().toString().equals(s)) {
                int M_i = Mmap.get(m[j].toString());
                if (TRACE_RELATIONS) out.println("Adding to stringToMethod: "+H_i+","+M_i);
                stringToMethod.add(H_i, M_i);
            }
        }
    }
    
    static void addToS(int V_i, jq_Field f, Collection c) {
        int F_i = Fmap.get(""+f);
        // TODO: special case for collection sets
        for (Iterator k = c.iterator(); k.hasNext(); ) {
            Node node2 = (Node) k.next();
            if (FILTER_NULL && isNullConstant(node2))
                continue;
            int V2_i = Vmap.get(node2.toString());
            if (TRACE_RELATIONS) out.println("Adding to S: "+V_i+","+F_i+","+V2_i);
            S.add(V_i, F_i, V2_i);
        }
    }
    
    static void addToL(int V_i, jq_Field f, Collection c) {
        int F_i = Fmap.get(""+f);
        for (Iterator k = c.iterator(); k.hasNext(); ) {
            Node node2 = (Node) k.next();
            if (FILTER_NULL && isNullConstant(node2))
                continue;
            int V2_i = Vmap.get(node2.toString());
            if (TRACE_RELATIONS) out.println("Adding to L: "+V_i+","+F_i+","+V2_i);
            L.add(V_i, F_i, V2_i);
        }
    }
    
    static void addToA(int V_i, int V2_i) {
        if (TRACE_RELATIONS) out.println("Adding to A: "+V_i+","+V2_i);
        A.add(V_i, V2_i);
    }
    
    static void addToMret(int M_i, Node node) {
        int V_i = Vmap.get(node.toString());
        if (TRACE_RELATIONS) out.println("Adding to Mret: "+M_i+","+V_i);
        Mret.add(M_i, V_i);
    }
    
    static void addToMthr(int M_i, Node node) {
        int V_i = Vmap.get(node.toString());
        if (TRACE_RELATIONS) out.println("Adding to Mthr: "+M_i+","+V_i);
        Mthr.add(M_i, V_i);
    }
    
    /*
    static void addToMV(int M_i, int V_i) {
        if (TRACE_RELATIONS) out.println("Adding to mV: "+M_i+","+V_i);
        mV.add(M_i, V_i);
    }*/
    
    static void addToIret(int I_i, Node node) {
        int V_i = Vmap.get(node.toString());
        if (TRACE_RELATIONS) out.println("Adding to Iret: "+I_i+","+V_i);
        Iret.add(I_i, V_i);
    }
    
    static void addToIthr(int I_i, Node node) {
        int V_i = Vmap.get(node.toString());
        if (TRACE_RELATIONS) out.println("Adding to Ithr: "+I_i+","+V_i);
        Ithr.add(I_i, V_i);
    }
    
    static void addToFormal(int M_i, int z, Node node) {
        int V_i = Vmap.get(node.toString());
        if (TRACE_RELATIONS) out.println("Adding to formal: "+M_i+","+z+","+V_i);
        formal.add(M_i, z, V_i);
    }
    
    static void addToActual(int I_i, int z, Collection c) {
        for (Iterator k = c.iterator(); k.hasNext(); ) {
            Node node = (Node) k.next();
            if (FILTER_NULL && isNullConstant(node))
                continue;
            int V_i = Vmap.get(node.toString());
            if (TRACE_RELATIONS) out.println("Adding to actual: "+I_i+","+z+","+V_i);
            actual.add(I_i, z, V_i);
        }
    }
    
    static void addToMI(int M_i, int I_i, jq_Method name) {
        int oldSize = Nmap.size();
        int N_i = Nmap.get(""+name);
        if (N_i >= oldSize) {
            // New virtual method name.
            visitName(name);
        }
        if (TRACE_RELATIONS) out.println("Adding to mI: "+M_i+","+I_i+","+N_i);
        mI.add(M_i, I_i, N_i);
    }
    
    static void addToIE0(int I_i, jq_Method m) {
        int M_i = Mmap.get(m.toString());
        if (TRACE_RELATIONS) out.println("Adding to IE0: "+I_i+","+M_i+","+Imap.get(I_i)+","+m);
        IE0.add(I_i, M_i);
    }
    
    static void addToVT(int V_i, jq_Reference t) {
        int oldSize = Tmap.size();
        int T_i = Tmap.get(""+t);
        if (T_i >= oldSize) {
            // New type discovered.
            visitType(t);
        }
        if (TRACE_RELATIONS) out.println("Adding to vT: "+V_i+","+T_i);
        vT.add(V_i, T_i);
    }
    
    static void addToHT(int H_i, jq_Reference t) {
        int oldSize = Tmap.size();
        int T_i = Tmap.get(""+t);
        if (T_i >= oldSize) {
            // New type discovered.
            visitType(t);
        }
        if (TRACE_RELATIONS) out.println("Adding to hT: "+H_i+","+T_i);
        hT.add(H_i, T_i);
    }
    
    static void addToCHA(int T1_i, int N_i) {
        String N_s = (String) Nmap.get(N_i);
        if (N_s.equals("null")) return;
        jq_Method n = (jq_Method) jq_Member.parseMember(N_s);
        String T1_s = (String) Tmap.get(T1_i);
        jq_Reference t1 = null;
        if (T1_s != null && !T1_s.equals("null") && !T1_s.equals("NULL_TYPE"))
            t1 = (jq_Reference) jq_Type.parseType(T1_s);
        jq_Method m;
        if (n.isStatic()) {
            if (t1 != null) return;
            m = n;
        } else {
            if (t1 == null ||
                t1 == jq_NullType.NULL_TYPE ||
                !t1.isSubtypeOf(n.getDeclaringClass())) return;
            m = t1.getVirtualMethod(n.getNameAndDesc());
        }
        if ((m == javaLangObject_clone && t1 != object_class) || n == javaLangObject_fakeclone) {
            m = fakeCloneIfNeeded(t1); // for t.clone()
            int M_i = Mmap.get(m.toString());
            int N2_i = Nmap.get(javaLangObject_fakeclone.toString());
            cha.add(T1_i, N2_i, M_i); // for super.clone()
        }
        if (m == null) return;
        
        if (USE_BOGUS_SUMMARIES && m != null) {
            jq_Method replacement = PA.getBogusSummaryProvider().getReplacementMethod(m);
            if (replacement != null) {
                cha.add(T1_i, Nmap.get(replacement.toString()), Mmap.get(replacement.toString()));
                return;
            }
        }
        
        if (USE_REFLECTION_PROVIDER && m != null && ReflectionInformationProvider.isNewInstance(n)){
            Collection/*<jq_Method>*/ targets = PA.getReflectionProvider().getNewInstanceTargets(n);
            if (targets != null){
                for (Iterator iter = targets.iterator(); iter.hasNext();){
                    jq_Method target = (jq_Method) iter.next();
                    cha.add(T1_i, Nmap.get(target.toString()), Mmap.get(target.toString()));                            
                }
                //return;
            }
        }
        
        // default case
        int M_i = Mmap.get(m.toString());
        if (TRACE_RELATIONS) out.println("Adding to cha: "+T1_i+","+N_i+","+M_i+" = "+t1+","+n.getName()+","+m);
        cha.add(T1_i, N_i, M_i);
    }
    
    static void visitName(jq_Method name) {
        int N_i = Nmap.get(""+name);
        if (name == null) return;
        name.getDeclaringClass().prepare();
        for (int T_i = 0; T_i < Tmap.size(); ++T_i) {
            addToCHA(T_i, N_i);
        }
    }
    
    static jq_Method fakeCloneIfNeeded(jq_Type t) {
        jq_Method m = javaLangObject_clone;
        if (t instanceof jq_Class) {
            jq_Class c = (jq_Class)t;
            if (!c.isInterface() && c.implementsInterface(cloneable_class)) {
                m = jq_FakeInstanceMethod.fakeMethod(c, MethodSummary.fakeCloneName, "()"+t.getDesc());
                int M_i = Mmap.get(m.toString());
                // TODO: add to something other than roots.
                if (roots.add(M_i)) {
                    if (TRACE_RELATIONS) out.println("Adding to roots: "+M_i);
                    visitMethod(m);
                }
            }
        }
        // TODO: handle cloning of arrays
        return m;
    }
    
    static void visitType(jq_Reference t1) {
        int T1_i = Tmap.get(""+t1);
        if (t1 != null) t1.prepare();
        if (t1 != null && !t1.isPrepared()) {
            System.out.println("Cannot load "+t1);
            return;
        }
        for (int T2_i = 0; T2_i < Tmap.size(); ++T2_i) {
            String s = (String) Tmap.get(T2_i);
            jq_Reference t2;
            if (s.equals("null") || s.equals("NULL_TYPE")) t2 = null;
            else t2 = (jq_Reference) jq_Type.parseType(s);
            if (t2 != null) t2.prepare();
            if (t2 != null && !t2.isPrepared()) {
                System.out.println("Cannot load "+t2);
                continue;
            }
            if (t2 == null || (t1 != null && t2.isSubtypeOf(t1))) {
                if (TRACE_RELATIONS) out.println("Adding to aT: "+T1_i+","+T2_i);
                aT.add(T1_i, T2_i);
            }
            if (t1 == null || (t2 != null && t1.isSubtypeOf(t2))) {
                if (TRACE_RELATIONS) out.println("Adding to aT: "+T2_i+","+T1_i);
                aT.add(T2_i, T1_i);
            }
        }
        if (t1 instanceof jq_Class) {
            jq_Class c = (jq_Class) t1;
            jq_Method m = c.getDeclaredInstanceMethod(new jq_NameAndDesc("<init>", "()V"));
            if (m != null) {
                int M_i = Mmap.get(m.toString());
                if (TRACE_RELATIONS) out.println("Adding to defaultConstructor: "+T1_i+","+M_i);
                defaultConstructor.add(T1_i, M_i);
            }
            jq_Method[] ms = c.getDeclaredInstanceMethods();
            Utf8 init = Utf8.get("<init>");
            for (int i = 0; i < ms.length; ++i) {
                if (ms[i].getName() == init) {
                    int M_i = Mmap.get(ms[i].toString());
                    if (TRACE_RELATIONS) out.println("Adding to allConstructors: "+T1_i+","+M_i);
                    allConstructors.add(T1_i, M_i);
                }
            }
            for (Iterator i = stringNodes.iterator(); i.hasNext(); ) {
                Node n = (Node) i.next();
                String s = (String) MethodSummary.stringNodes2Values.get(n);
                int H_i = Hmap.get(n.toString());
                handleString(H_i, s, c);
            }
        }
        for (int N_i = 0; N_i < Nmap.size(); ++N_i) {
            String s = (String) Nmap.get(N_i);
            if (s.equals("null")) continue;
            jq_Method n = (jq_Method) jq_Member.parseMember(s);
            if (n == null) continue;
            n.getDeclaringClass().prepare();
            addToCHA(T1_i, N_i);
        }
    }
    
    static boolean isNullConstant(Node node) {
        if (node instanceof ConcreteTypeNode || node instanceof ConcreteObjectNode) {
            jq_Reference type = node.getDeclaredType();
            if (type == null || type == jq_NullType.NULL_TYPE) {
                return true;
            }
        }
        return false;
    }
    
    static void addToRoots(jq_Method m) {
        int M_i = Mmap.get(m.toString());
        if (roots.add(M_i)) {
            if (TRACE_RELATIONS) out.println("Adding to roots: "+M_i);
            visitMethod(m);
        }
    }
    
    static void addClassInitializer(jq_Class c) {
        jq_Method m = c.getClassInitializer();
        if (m != null) {
            addToRoots(m);
        }
    }
    
    static int opn;
    
    static void visitMethod(jq_Method m) {
        Assert._assert(m != null);
        Assert._assert(m.getDeclaringClass() != null);
        
        if (TRACE) out.println("Visiting method "+m);
        m.getDeclaringClass().prepare();
        
        int M_i = Mmap.get(m.toString());
        
        // Skip visiting some methods.
        if (skipMethod.contains(0, BigInteger.valueOf(M_i))) {
            out.println("Skipping generation of method "+m);
            return;
        }
        MethodSummary ms = MethodSummary.getSummary(m);
        
        if (m.getBytecode() == null && ms == null) {
            // todo: parameters passed into native methods.
            // build up 'Mret'
            jq_Type retType = m.getReturnType();
            if (retType instanceof jq_Reference) {
                Node node = UnknownTypeNode.get((jq_Reference) retType);
                addToMret(M_i, node);
                visitNode(node);
            }
            return;
        }
        
        if (TRACE) out.println("Visiting method summary "+ms);
        
        addClassInitializer(ms.getMethod().getDeclaringClass());
        
        // build up 'formal'
        int offset;
        Node thisparam;
        if (ms.getMethod().isStatic()) {
            thisparam = GlobalNode.GLOBAL;
            offset = 0;
        } else {
            thisparam = ms.getParamNode(0);
            offset = 1;
        }
        addToFormal(M_i, 0, thisparam);
        if (m.isSynchronized() && !m.isStatic()) {
            //addToSync(thisparam);
            //addToMSync(m);
        }
        int nParams = ms.getNumOfParams();
        for (int i = offset; i < nParams; ++i) {
            Node node = ms.getParamNode(i);
            if (node == null) continue;
            addToFormal(M_i, i+1-offset, node);
        }
        
        for (Iterator i = ms.getSyncedVars().iterator(); i.hasNext(); ) {
            Node node = (Node) i.next();
            if (FILTER_NULL && isNullConstant(node))
                continue;
            if (TRACE) out.println("Sync on: "+node);
            //addToSync(node);
        }
        
        // build up 'mI', 'actual', 'Iret', 'Ithr'
        for (Iterator i = ms.getCalls().iterator(); i.hasNext(); ) {
            ProgramLocation mc = (ProgramLocation) i.next();
            if (TRACE) out.println("Visiting call site "+mc);
            int I_i = Imap.get(LoadedCallGraph.mapCall(mc).toString());
            jq_Method target = mc.getTargetMethod();

            jq_Method replacement = null;
            if (USE_BOGUS_SUMMARIES) {
                replacement = PA.getBogusSummaryProvider().getReplacementMethod(target);
                if (replacement != null) {
                    jq_Method oldTarget = target;
                    target = replacement;
                    Quad q = ( (ProgramLocation.QuadProgramLocation) mc).getQuad();
                    if(!PA.getBogusSummaryProvider().hasStaticReplacement(replacement)){
                        Operand.MethodOperand methodOp = Operator.Invoke.getMethod(q);
                        Assert._assert(methodOp.getMethod() == oldTarget);
                        methodOp.setMethod(replacement);
                        
                        if(!replacement.isStatic()){
                            Operand.ParamListOperand listOp = Operator.Invoke.getParamList(q);
                            if(listOp.get(0).getType() == oldTarget.getDeclaringClass()){
                                listOp.get(0).setType(replacement.getDeclaringClass());
                            }
                        }
                    }
                }
            }            
            if (target.isStatic()){
                addClassInitializer(target.getDeclaringClass());
            }
            
            Set thisptr;
            if ((replacement != null) && PA.getBogusSummaryProvider().hasStaticReplacement(replacement)) {                
                thisptr = Collections.singleton(GlobalNode.GLOBAL);
                addToActual(I_i, 0, thisptr);
                offset = 0;
            } else {
                if (target.isStatic()) {
                    thisptr = Collections.singleton(GlobalNode.GLOBAL);
                    offset = 0;
                } else {
                    thisptr = ms.getNodesThatCall(mc, 0);
                    offset = 1;
                }
                addToActual(I_i, 0, thisptr);
            }            
            
            Collection/*<jq_Method>*/ targets = null;
            if (USE_REFLECTION_PROVIDER && ReflectionInformationProvider.isNewInstance(target)){                
                targets = PA.getReflectionProvider().getNewInstanceTargets(m);
                if (targets != null){
                    if (PA.TRACE_REFLECTION)  {
                        System.out.println("Replacing a call to " + target + " with " + targets); 
                    }
                
                    for (Iterator iter = targets.iterator(); iter.hasNext();){
                        jq_Method newTarget = (jq_Method) iter.next();
                        
                        if (newTarget instanceof jq_Initializer){
                            jq_Initializer constructor = (jq_Initializer) newTarget;
                            jq_Type type = constructor.getDeclaringClass();
                                                        
                            Node node = ms.getRVN(mc);
                            if (node != null) {
                                MethodSummary.ConcreteTypeNode h = ConcreteTypeNode.get((jq_Reference) type);
                                int V_i = Vmap.get(node.toString());
                                addToVP0(V_i, h);
                            }
                        }
                        
                        if (PA.TRACE_REFLECTION) {
                            System.out.println("Adding a reflective call to " + newTarget);
                        }
                        addToMI(M_i, I_i, newTarget);
                        addToIE0(I_i, newTarget);
                    }
                }
            }
            
            if (mc.isSingleTarget() ||
                (replacement != null && !PA.getBogusSummaryProvider().hasStaticReplacement(replacement))) 
            {
                if (target == javaLangObject_clone) {
                    addToMI(M_i, I_i, javaLangObject_fakeclone);
                }
                
                // statically-bound, single target call
                addSingleTargetCall(thisptr, mc, I_i, target);
                addToMI(M_i, I_i, null);
            } else {
                // virtual call
                addToMI(M_i, I_i, target);
            }
            
            jq_Type[] params = mc.getParamTypes();
            int k = offset;
            for ( ; k < params.length; ++k) {
                Set s = ms.getNodesThatCall(mc, k);
                addToActual(I_i, k+1-offset, s);
            }
            Node node = ms.getRVN(mc);
            if (node != null) {
                addToIret(I_i, node);
            }
            node = ms.getTEN(mc);
            if (node != null) {
                addToIthr(I_i, node);
            }
        }
       
        // build up 'mV', 'vP', 'S', 'L', 'Mret', 'Mthr'
        for (Iterator i = ms.nodeIterator(); i.hasNext(); ) {
            Node node = (Node) i.next();
            
            if (FILTER_NULL && isNullConstant(node))
                continue;

            // get a variable for this node
            //int V_i = Vmap.get(node);
            //addToMV(M_i, V_i);
            
            if (ms.getReturned().contains(node)) {
                addToMret(M_i, node);
            }
            
            if (ms.getThrown().contains(node)) {
                addToMthr(M_i, node);
            }
            
            visitNode(node);
        }

        for (Iterator i = ms.getCastMap().entrySet().iterator(); i.hasNext(); ) {
            Map.Entry e = (Map.Entry)i.next();
            Node from = (Node)((Pair)e.getKey()).left;
            if (FILTER_NULL && isNullConstant(from))
                continue;
            CheckCastNode to = (CheckCastNode)e.getValue();
            int V_i = Vmap.get(to.toString());
            addToA(V_i, Vmap.get(from.toString()));
        }
    }
    
    static jq_Class object_class = PrimordialClassLoader.getJavaLangObject();
    static jq_Method javaLangObject_clone;
    static {
        object_class.prepare();
        javaLangObject_clone = object_class.getDeclaredInstanceMethod(new jq_NameAndDesc("clone", "()Ljava/lang/Object;"));
    }
    
    static jq_Class class_class = PrimordialClassLoader.getJavaLangClass();
    static jq_Method javaLangClass_newInstance;
    static {
        class_class.prepare();
        javaLangClass_newInstance = class_class.getDeclaredInstanceMethod(new jq_NameAndDesc("newInstance", "()Ljava/lang/Object;"));
        Assert._assert(javaLangClass_newInstance != null);
    }
    
    static jq_Class cloneable_class = (jq_Class) PrimordialClassLoader.loader.getOrCreateBSType("Ljava/lang/Cloneable;");
    static jq_Class throwable_class = (jq_Class) PrimordialClassLoader.getJavaLangThrowable();
    static jq_Method javaLangObject_fakeclone = jq_FakeInstanceMethod.fakeMethod(object_class, 
                                                MethodSummary.fakeCloneName, "()Ljava/lang/Object;");
    
    static void addSingleTargetCall(Set thisptr, ProgramLocation mc, int I_i, jq_Method target) {
        Assert._assert(target != null);
        addToIE0(I_i, target);
    }
    
    static void visitNode(Node node) {
        if (TRACE) 
            out.println("Visiting node "+node);
       
        if (FILTER_NULL && isNullConstant(node))
            return;
        
        int V_i = Vmap.get(node.toString());
        
        addToVT(V_i, node.getDeclaredType());
        
        if (node instanceof ConcreteTypeNode) {
            addToVP0(V_i, node);
            if (node.getDeclaredType() instanceof jq_Class)
                addClassInitializer((jq_Class) node.getDeclaredType());
        } else if (node instanceof ConcreteObjectNode ||
                   node instanceof UnknownTypeNode ||
                   node == GlobalNode.GLOBAL) 
        {
            addToVP0(V_i, node);
        } else if (node instanceof GlobalNode) {
            int V2_i = Vmap.get(GlobalNode.GLOBAL.toString());
            addToA(V_i, V2_i);
            addToA(V2_i, V_i);
        }
        
        for (Iterator j = node.getAllEdges().iterator(); j.hasNext(); ) {
            Map.Entry e = (Map.Entry) j.next();
            jq_Field f = (jq_Field) e.getKey();
            Collection c;
            if (e.getValue() instanceof Collection)
                c = (Collection) e.getValue();
            else
                c = Collections.singleton(e.getValue());
            addToS(V_i, f, c);
        }
        
        for (Iterator j = node.getAccessPathEdges().iterator(); j.hasNext(); ) {
            Map.Entry e = (Map.Entry) j.next();
            jq_Field f = (jq_Field) e.getKey();
            Collection c;
            if (e.getValue() instanceof Collection)
                c = (Collection) e.getValue();
            else
                c = Collections.singleton(e.getValue());
            addToL(V_i, f, c);
            if (node instanceof GlobalNode)
                addClassInitializer(f.getDeclaringClass());
        }
    }
    
    static Collection readClassesFromFile(String fname) throws IOException {
        BufferedReader r = null;
        try {
            r = new BufferedReader(new FileReader(fname));
            Collection rootMethods = new ArrayList();
            String s = null;
            while ((s = r.readLine()) != null) {
                jq_Class c = (jq_Class) jq_Type.parseType(s);
                c.prepare();
                rootMethods.addAll(Arrays.asList(c.getDeclaredStaticMethods()));
            }
            return rootMethods;
        } finally {
            if (r != null) r.close();
        }
    }
    
    public static void main(String[] args) throws IOException, InstantiationException, IllegalAccessException, ClassNotFoundException {
        HostedVM.initialize();
        CodeCache.AlwaysMap = true;
        
        Collection rootMethods = null;
        if (args[0].startsWith("@")) {
            rootMethods = readClassesFromFile(args[0].substring(1));
        } else {
            jq_Class c = (jq_Class) jq_Type.parseType(args[0]);
            c.prepare();
            rootMethods = Arrays.asList(c.getDeclaredStaticMethods());
        }

        if (args.length > 1) {
            for (Iterator i = rootMethods.iterator(); i.hasNext(); ) {
                jq_Method sm = (jq_Method) i.next();
                if (args[1].equals(sm.getName().toString())) {
                    rootMethods = Collections.singleton(sm);
                    break;
                }
            }
        }
        
        BDDSolver solver = new BDDSolver();
        initDefaultFiles(solver);
        solver.load("pafly.datalog");
        initialize(solver);
        visitNode(GlobalNode.GLOBAL);
        for (Iterator i = ConcreteObjectNode.getAll().iterator(); i.hasNext(); ) {
            ConcreteObjectNode con = (ConcreteObjectNode) i.next();
            visitNode(con);
        }
        for (Iterator i = rootMethods.iterator(); i.hasNext(); ) {
            jq_Method m = (jq_Method) i.next();
            addToRoots(m);
        }
        
        saveAll(solver);
    }
    
    static void initDefaultFiles(BDDSolver solver) throws IOException {
        String sep = System.getProperty("file.separator");
        String basedir = solver.getBaseDir();
        if (basedir.length() > 0 && !basedir.endsWith(sep) && !basedir.endsWith("/")) {
            basedir += sep;
        }
        File f = new File(basedir);
        if (!f.exists()) {
            f.mkdirs();
        }
        f = new File(basedir+"fielddomains.pa");
        if (!f.exists()) {
            BufferedWriter w = null;
            try {
                w = new BufferedWriter(new FileWriter(f));
                w.write("V 1048576 var.map\n");
                w.write("H 262144 heap.map\n");
                w.write("T 8192 type.map\n");
                w.write("F 16384 field.map\n");
                w.write("I 32768 invoke.map\n");
                w.write("Z 32\n");
                w.write("N 8192 name.map\n");
                w.write("M 16384 method.map\n");
            } finally {
                if (w != null) w.close();
            }
        }
    }
    
    static void dumpCallGraph(String filename) throws IOException {
        System.out.print("Dumping call graph...");
        CallGraph callgraph = new CachedCallGraph(new PAFlyCG());
        BufferedWriter dos = null;
        try {
            dos = new BufferedWriter(new FileWriter(filename));
            LoadedCallGraph.write(callgraph, dos);
            System.out.println("done.");
        } finally {
            if (dos != null) dos.close();
        }
        
    }
    
    static boolean isWellFormed(String stringConst) {
        if(stringConst.equals(".")) {
            return false;
        }
        int dotCount = 0;
        for(int i = 0; i < stringConst.length(); i++){
            char ch = stringConst.charAt(i);
            
            if(ch == '.'){
                dotCount++;                
            } else {            
                if(ch != '$' && ch != '_' && !Character.isLetterOrDigit(ch)){
                    return false;                
                }      
            }
        }
        
        //if(dotCount == 0) return false;
        
        return true;
    }
    
    static jq_Class tryLoadingClass(String stringConst) {
        if(!isWellFormed(stringConst)) {
            if (TRACE) System.out.println("Not well formed.");
            return null;
        }
        try {
            jq_Type clazz = jq_Type.parseType(stringConst);
            if (TRACE) System.out.println("parseType returned: "+clazz);
            if (clazz instanceof jq_Class) {
                jq_Class c = (jq_Class) clazz;
                c.load();
                c.prepare();
                return c;
            } else {
                return null;
            }
        } catch (NoClassDefFoundError e) {
            //System.out.println(stringConst+" : "+e);
        } catch (java.lang.ClassCircularityError e) {
            System.out.println(stringConst+" CCE: "+e);
        }
        return null;
    }
    
    public static class PAFlyCG extends CallGraph {
        
        StringIndexMap methodMap = new StringIndexMap(Mmap, new Filter() {
            public Object map(Object o) {
                String s = (String) o;
                if (s.equals("null")) return null;
                return jq_Member.parseMember(s);
            }
        });
        
        /* (non-Javadoc)
         * @see joeq.Compiler.Quad.CallGraph#setRoots(java.util.Collection)
         */
        public void setRoots(Collection roots) {
            Assert.UNREACHABLE();
        }

        /* (non-Javadoc)
         * @see joeq.Compiler.Quad.CallGraph#getRoots()
         */
        public Collection getRoots() {
            BDD b = roots.getBDD().id();
            BDD c = roots.getBDDDomain(0).ithVar(Mmap.get("null"));
            b.applyWith(c, BDDFactory.diff);
            return new BDDSet(b, roots.getBDDDomain(0), methodMap);
        }

        /* (non-Javadoc)
         * @see joeq.Compiler.Quad.CallGraph#getTargetMethods(java.lang.Object, joeq.Compiler.Analysis.IPA.ProgramLocation)
         */
        public Collection getTargetMethods(Object context, ProgramLocation callSite) {
            callSite = LoadedCallGraph.mapCall(callSite);
            int I_i = Imap.get(callSite.toString());
            BDD I_bdd = IE.getBDDDomain(0).ithVar(I_i);
            BDD b = IE.getBDD().restrict(I_bdd);
            I_bdd.free();
            BDD c = IE.getBDDDomain(1).ithVar(Mmap.get("null"));
            b.applyWith(c, BDDFactory.diff);
            return new BDDSet(b, IE.getBDDDomain(1), methodMap);
        }
        
        /* (non-Javadoc)
         * @see joeq.Compiler.Quad.CallGraph#getAllMethods()
         */
        public Collection getAllMethods() {
            BDD b = roots.getBDD().id();
            BDD s = IE.getBDDDomain(0).set();
            b.orWith(IE.getBDD().exist(s));
            s.free();
            BDD c = roots.getBDDDomain(0).ithVar(Mmap.get("null"));
            b.applyWith(c, BDDFactory.diff);
            return new BDDSet(b, IE.getBDDDomain(1), methodMap);
        }
    }
    
    public static class StringIndexMap implements IndexedMap {
        
        IndexedMap map;
        Filter f;

        public StringIndexMap(IndexedMap m, Filter f) {
            this.map = m;
            this.f = f;
        }
        
        /* (non-Javadoc)
         * @see jwutil.collections.IndexedMap#get(java.lang.Object)
         */
        public int get(Object o) {
            return map.get(""+o);
        }

        /* (non-Javadoc)
         * @see jwutil.collections.IndexedMap#get(int)
         */
        public Object get(int i) {
            String s = (String) map.get(i);
            return f.map(s);
        }

        /* (non-Javadoc)
         * @see jwutil.collections.IndexedMap#contains(java.lang.Object)
         */
        public boolean contains(Object o) {
            return map.contains(""+o);
        }

        /* (non-Javadoc)
         * @see jwutil.collections.IndexedMap#iterator()
         */
        public Iterator iterator() {
            return new FilterIterator(map.iterator(), f);
        }

        /* (non-Javadoc)
         * @see jwutil.collections.IndexedMap#size()
         */
        public int size() {
            return map.size();
        }

        /* (non-Javadoc)
         * @see jwutil.collections.IndexedMap#dump(java.io.BufferedWriter)
         */
        public void dump(BufferedWriter out) throws IOException {
            Assert.UNREACHABLE();
        }

        /* (non-Javadoc)
         * @see jwutil.collections.IndexedMap#dumpStrings(java.io.BufferedWriter)
         */
        public void dumpStrings(BufferedWriter out) throws IOException {
            map.dumpStrings(out);
        }
        
    }
    
}
