// ClassHierarchyAnalysis.java, created Jul 6, 2004 5:36:59 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Iterator;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.Modifier;
import org.sf.bddbddb.util.IndexedMap;
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
    
    ClassHierarchyAnalysis(PAFromSource pa) {
        this.cha = pa.cha;
        this.pa = pa;
        this.Tmap = pa.Tmap;
        this.Nmap = pa.Nmap;
        this.Mmap = pa.Mmap;
        this.T = PAFromSource.T2;
        this.N = PAFromSource.N;
        this.M = PAFromSource.M;
        OBJECT = pa.OBJECT.getType();
    }
    
    IndexedMap Tmap;
    IndexedMap Nmap;
    IndexedMap Mmap;
    
    BDDDomain T, N, M;
    BDD cha;
    
    void addToCHA(Wrapper type, IMethodBinding name, IMethodBinding target) {
        int T_i = Tmap.get(type);
        int N_i = Nmap.get(new MethodWrapper(name));
        int M_i = Mmap.get(new MethodWrapper(target));
        
        //System.out.println("adding to CHA: "+pa.new TypeWrapper(type)+" / "
        //    +pa.new MethodWrapper(name)+" / "+pa.new MethodWrapper(target));
        
        BDD b = T.ithVar(T_i).andWith(N.ithVar(N_i)).andWith(M.ithVar(M_i));
        cha.orWith(b);
    }
    
    void calculateCHA() {
        for (Iterator i = Nmap.iterator(); i.hasNext(); ) {
            Object o = i.next();
            if (!(o instanceof MethodWrapper)) {
                continue;
            }
            MethodWrapper mw = (MethodWrapper) o;
            IMethodBinding name = mw.getBinding();
            calculateCHA(name);
        }
    }
    
    void calculateCHA(IMethodBinding name) {
        IMethodBinding objTarget = calculateVirtualTarget(OBJECT, name);
        
        for (Iterator i = Tmap.iterator(); i.hasNext(); ) {
            Object o = i.next();
            ITypeBinding type;
            if (o instanceof TypeWrapper) {
                TypeWrapper tw = (TypeWrapper) o;
                type = tw.getType();
                IMethodBinding target = calculateVirtualTarget(type, name);
                if (target != null) {
                    addToCHA((Wrapper)o, name, target);
                }
            } else {
                if (objTarget == null || 
                    !((StringWrapper)o).getString().endsWith("[]")) continue;
                addToCHA((Wrapper)o, name, objTarget);             
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
                    if (typesMatch(types1, types2)) {
                        method = methods[i];
                        break;
                    }
                }
            }
            if (method != null) {
                int mod = method.getModifiers();
                if (method.isConstructor() || Modifier.isAbstract(mod) || Modifier.isPrivate(mod) || Modifier.isStatic(mod)) return null;
                return method;
            }
            //if (type.getKey().equals(OBJECT.getKey())) break;
            type = type.getSuperclass();
            if (type == null) return null;
        }
    }

    boolean typesMatch(ITypeBinding[] types1, ITypeBinding[] types2) {
        if (types1.length != types2.length) return false;
        
        for (int i = 0; i < types1.length; i++) {
            if (!types1[i].getKey().equals(types2[i].getKey())) return false;
        }
        
        return true;
    }
    
}
