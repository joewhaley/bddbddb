// ClassHierarchyAnalysis.java, created Jul 6, 2004 5:36:59 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Arrays;
import java.util.Iterator;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.Modifier;
import org.sf.bddbddb.PAFromSource.MethodWrapper;
import org.sf.bddbddb.PAFromSource.TypeWrapper;
import org.sf.bddbddb.util.IndexMap;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;

/**
 * ClassHierarchyAnalysis
 * 
 * @author jwhaley
 * @version $Id$
 */
public class ClassHierarchyAnalysis {
    
    PAFromSource pa;
    ITypeBinding OBJECT;
    
    ClassHierarchyAnalysis(PAFromSource pa, AST ast) {
        this.pa = pa;
        this.Tmap = pa.Tmap;
        this.Nmap = pa.Nmap;
        this.Mmap = pa.Mmap;
        this.T = pa.T1;
        this.N = pa.N;
        this.M = pa.M;
        this.cha = pa.bdd.zero();
        OBJECT = ast.resolveWellKnownType("java.lang.Object");
    }
    
    IndexMap Tmap;
    IndexMap Nmap;
    IndexMap Mmap;
    
    BDDDomain T, N, M;
    BDD cha;
    
    void addToCHA(ITypeBinding type, IMethodBinding name, IMethodBinding target) {
        int T_i = Tmap.get(pa.new TypeWrapper(type));
        int N_i = Nmap.get(pa.new MethodWrapper(name));
        int M_i = Mmap.get(pa.new MethodWrapper(target));
        BDD b = T.ithVar(T_i).andWith(N.ithVar(N_i)).andWith(M.ithVar(M_i));
        cha.orWith(b);
    }
    
    BDD calculateCHA() {
        for (Iterator i = Nmap.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (!(o instanceof MethodWrapper)) continue;
            MethodWrapper mw = (MethodWrapper) o;
            IMethodBinding name = mw.method;
            calculateCHA(name);
        }
        return cha;
    }
    
    void calculateCHA(IMethodBinding name) {
        for (Iterator i = Tmap.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (!(o instanceof TypeWrapper)) continue;
            TypeWrapper tw = (TypeWrapper) o;
            ITypeBinding type = tw.type;
            IMethodBinding target = calculateVirtualTarget(type, name);
            if (target != null) {
                addToCHA(type, name, target);
            }
        }
    }
    
    IMethodBinding calculateVirtualTarget(ITypeBinding type, IMethodBinding name) {
        if (type.isArray() || type.isInterface()) type = OBJECT;
        for (;;) {
            IMethodBinding[] methods = type.getDeclaredMethods();
            IMethodBinding method = null;
            for (int i = 0; i < methods.length; ++i) {
                if (name.getName().equals(methods[i].getName())) {
                    ITypeBinding[] types1 = name.getParameterTypes();
                    ITypeBinding[] types2 = methods[i].getParameterTypes();
                    if (Arrays.equals(types1, types2)) {
                        method = methods[i];
                        break;
                    }
                }
            }
            if (method != null) {
                int mod = method.getModifiers();
                if (!Modifier.isAbstract(mod) && !Modifier.isPrivate(mod) && !Modifier.isStatic(mod)) {
                    return method;
                }
            }
            if (type == OBJECT) break;
            type = type.getSuperclass();
        }
        return null;
    }
    
}