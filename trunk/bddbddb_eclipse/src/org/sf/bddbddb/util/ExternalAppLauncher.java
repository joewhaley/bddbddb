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
import org.sf.bddbddb.PAFromSource;

/**
 * ExternalAppLauncher
 * 
 * @author jwhaley
 * @version $Id$
 */
public class ExternalAppLauncher {
    
    public static int launch(String[] cmd) {
        int r = -1;
        try {
            Process p = Runtime.getRuntime().exec(cmd);
            StreamGobbler output = new StreamGobbler(p.getInputStream(), "OUT");
            StreamGobbler error = new StreamGobbler(p.getErrorStream(), "ERR", System.err);

            output.start();
            error.start();
            
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
        String joeqDir = loadPath + "joeq_core.jar";
        String javabddDir = loadPath + "javabdd.jar";
        String appDir = System.getProperty("pas.apppath", "");
        String pathsep = System.getProperty("path.separator");
        String classpath = joeqDir+pathsep+javabddDir+pathsep+appDir;
        String mainClassName = "joeq.Main.GenRelations";
        
        try {
            File tempFile = File.createTempFile("classes", "txt");
            BufferedWriter out = new BufferedWriter(new FileWriter(tempFile));
            for (Iterator i = classNames.iterator(); i.hasNext(); ) {
                out.write(i.next()+"\n");
            }
            out.close();
            String[] cmd = new String[] {
                "java", "-mx256m",
                "-cp", classpath,
                "-Dpa.dumppath="+loadPath,
                "-Dpa.dumpfly",
                "-Dpa.fullcha",
                "-Dpa.addinstancemethods",
                "-Dpa.autodiscover=no",
                "-Dbddordering="+varorder,
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
    
    public static int callBddBddb(PAFromSource pa) {
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
}
