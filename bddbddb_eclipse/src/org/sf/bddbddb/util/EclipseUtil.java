// EclipseUtil.java, created Jul 28, 2004 6:40:18 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.util;

import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;

/**
 * EclipseUtil
 * 
 * @author jwhaley
 * @version $Id$
 */
public class EclipseUtil {
    
    public static String getFullyQualifiedClassName(IClassFile e2) {
        // .class file
        StringBuffer sb = new StringBuffer();
        String classFileName = e2.getElementName();
        sb.append(classFileName.substring(0, classFileName.length() - 6));
        IJavaElement e = e2.getParent();
        if (e instanceof IPackageFragment) {
            String packageName = e.getElementName();
            if (packageName.length() > 0) sb.insert(0, packageName + ".");
        } else {
            // unknown!
            return null;
        }
        return sb.toString();
    }
    
    /**
     * Return the fully-qualified class name corresponding to the given Eclipse
     * type. Example: java.util.Hashtable$Entry
     */
    public static String getFullyQualifiedClassName(IType t) {
        StringBuffer sb = new StringBuffer();
        IJavaElement e = t;
        e = e.getParent();
        if (e instanceof IClassFile) {
            // .class file
            String classFileName = e.getElementName();
            sb.append(classFileName.substring(0, classFileName.length() - 6));
        } else {
            while (e instanceof IType) {
                sb.insert(0, e.getElementName() + "$");
                e = e.getParent();
            }
            if (e instanceof ICompilationUnit) {
                // .java file
                sb.append(t.getElementName());
            } else {
                // unknown!
                return null;
            }
        }
        e = e.getParent();
        if (e instanceof IPackageFragment) {
            String packageName = e.getElementName();
            if (packageName.length() > 0) sb.insert(0, packageName + ".");
        } else {
            // unknown!
            return null;
        }
        return sb.toString();
    }
    
}
