// CodeFragment.java, created Jan 25, 2005 5:41:21 PM 2005 by jwhaley
// Copyright (C) 2005 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.StringTokenizer;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Method;
import net.sf.javabdd.BDD;

/**
 * CodeFragment
 * 
 * @author jwhaley
 * @version $Id$
 */
public class CodeFragment {

    String fragment;
    Method method;
    
    /**
     * @param string
     */
    public CodeFragment(String string) {
        this.fragment = string;
    }

    public static File findWritablePath() {
        // Find a place for a temp file in classpath.
        String cp = System.getProperty("java.class.path");
        StringTokenizer st = new StringTokenizer(cp, System.getProperty("path.separator"));
        while (st.hasMoreTokens()) {
            String p = st.nextToken();
            File f = new File(p);
            if (!f.isDirectory()) continue;
            if (!f.canWrite()) continue;
            return f;
        }
        return null;
    }
    
    Class genClass() {
        File path = findWritablePath();
        try {
            // Create temp file.
            File temp = File.createTempFile("frag", ".class", path);
            
            // Delete temp file when program exits.
            temp.deleteOnExit();
            
            // Get class name from file name.
            String className = temp.getName();
            className = className.substring(0, className.length()-6);
            
            // Write to temp file
            BufferedWriter out = new BufferedWriter(new FileWriter(temp));
            out.write("public class ");
            out.write(className);
            out.write(" {\n    public static void go(InferenceRule rule) {\n");
            out.write(fragment);
            out.write("\n    }\n}\n");
            out.close();
        } catch (IOException e) {
        }
        return null;
    }
    
    /**
     * @param rule
     * @param oldValue
     */
    public void invoke(BDDInferenceRule rule, BDD oldValue) {
        
    }
    
}
