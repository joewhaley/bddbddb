// ExternalAppLauncher.java, created Jul 28, 2004 6:00:31 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.util;

import java.util.Collection;
import java.util.Iterator;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.net.URL;
import org.eclipse.core.runtime.Platform;
import org.sf.bddbddb.PAFromSource;
import org.sf.bddbddb.eclipse.EclipsePlugin;

/**
 * ExternalAppLauncher
 * 
 * @author jwhaley
 * @version $Id$
 */
public class ExternalAppLauncher {
    static String installPath;
    
    
    static {
        // this code should work only on windows.
        try {
            URL install = EclipsePlugin.getDefault().getBundle().getEntry("/");
            URL dir = Platform.resolve(install);
            
            installPath = dir.getPath().substring(1);
            installPath = installPath.replace('/','\\');
            System.out.println("install path: " + installPath);
            
        } catch (IOException e) {
            e.printStackTrace();
        }
        
    }
    
    public static int launch(String[] cmd) {
        int r = -1;
        try {
            Process p = Runtime.getRuntime().exec(cmd);
            InputStreamGobbler output = new InputStreamGobbler(p.getInputStream(), "OUT");
            InputStreamGobbler error = new InputStreamGobbler(p.getErrorStream(), "ERR", System.err);
            OutputStreamGobbler input = new OutputStreamGobbler(p.getOutputStream());

            output.start();
            error.start();
            input.start();
            
            r = p.waitFor(); 
            
        } catch (Exception e) {
            e.printStackTrace();
        }
        return r;
    }
    
    public static void callJoeqGenRelations(Collection classNames, 
        String varorder) {
        String loadPath = System.getProperty("pas.loadpath", "");
        if (loadPath.length() > 0) {
            String sep = System.getProperty("file.separator", "/");
            if (!loadPath.endsWith(sep))
                loadPath += sep;
        }
        
        String curDir = System.getProperty("user.dir");
        String joeqDir = installPath + "joeq_core.jar";
        String javabddDir = installPath + "javabdd.jar";
        String appDir = System.getProperty("pas.apppath", "");
        String pathsep = System.getProperty("path.separator");
        String classpath = joeqDir+pathsep+javabddDir
                            +pathsep+appDir;
        String mainClassName = "joeq.Main.GenRelations";
        
        try {
            File tempFile = File.createTempFile("classes", "txt");
            BufferedWriter out = new BufferedWriter(new FileWriter(tempFile));
            for (Iterator i = classNames.iterator(); i.hasNext(); ) {
                out.write(i.next()+"\n");
            }
            out.close();
            String[] cmd = new String[] {
                "java", "-mx640m",
                "-cp", classpath,
                "-Dpa.dumppath="+loadPath,
                "-Dpa.dumpfly",
                "-Dpa.fullcha",
                "-Dpa.addinstancemethods",
                "-Dpa.autodiscover=no",
                "-Dbddordering="+"N_F_I_M2_M_Z_V2xV1_T1_H2_T2_H1",//varorder,
                mainClassName, "@"+tempFile.getAbsolutePath() };
            
            int r = launch(cmd);
            
            tempFile.delete();
            
            if (r != 0) {
                System.out.println("joeq failed: " + r);
                return;
            }
            
        } catch (IOException x) {
            x.printStackTrace();
        }        
    }
    
    public static int computeCallgraph(PAFromSource pa) {
        String dumpPath = System.getProperty("pas.dumppath", "");
        if (dumpPath.length() > 0) {
            String sep = System.getProperty("file.separator", "/");
            if (!dumpPath.endsWith(sep))
                dumpPath += sep;
        }
        //File f = new File("c:\\runtime-workspace\\joeq_test\\");
        String path = installPath + "pafly.datalog";
        String bddbddb = installPath + "bddbddb.jar";
        
        String[] cmd = new String[] {"java", 
            "-jar", "-mx512m",
            "-Dbasedir="+dumpPath,
            bddbddb, path }; 

        int r = launch(cmd);
        if (r != 0) {
            pa.out.println("bddbddb failed: " + r);
            return r;
        }
        
        pa.out.println("dumping callgraph...");
        try {
            MultiMap mm = pa.parseIETuples(dumpPath + "IE.rtuples");
            pa.writeCallgraph(dumpPath + "callgraph", mm);
            pa.out.println("callgraph dumped.");
        } catch (IOException x) {
            x.printStackTrace();
        }
        return r;
    }
    
    public static int genericize(PAFromSource pa) {
        String dumpPath = System.getProperty("pas.dumppath", "");
        if (dumpPath.length() > 0) {
            String sep = System.getProperty("file.separator", "/");
            if (!dumpPath.endsWith(sep))
                dumpPath += sep;
        }
        
        String path = installPath + "genericize.datalog";
        String bddbddb = installPath + "bddbddb.jar";
        
        String[] cmd = new String[] {"java", 
            "-jar", "-mx640m",
            "-Dbasedir="+dumpPath,
            bddbddb, path }; 

        int r = launch(cmd);
        if (r != 0) {
            pa.out.println("bddbddb failed: " + r);
            return r;
        }
        
        pa.out.println("bddbddb complete...");
       //XXX
        return r;
    }
}
