/*
 * Created on Jul 14, 2004
 */
package org.sf.bddbddb.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;

/**
 * Based on http://www.javaworld.com/javaworld/jw-12-2000/jw-1229-traps.html
 * 
 * @author jzhuang
 */

public class StreamGobbler extends Thread
{
    InputStream is;
    String type;
    PrintStream out;
    
    public StreamGobbler(InputStream is, String type)
    {
        this(is, type, System.out);
    }
    
    public StreamGobbler(InputStream is, String type, PrintStream o)
    {
        this.is = is;
        this.type = type;
        out = o;
    }
    
    public void run()
    {
        try
        {
            InputStreamReader isr = new InputStreamReader(is);
            BufferedReader br = new BufferedReader(isr);
            String line=null;
            while ( (line = br.readLine()) != null) {
                out.println(type + "> " + line);    
            }
            br.close();
            
        } catch (IOException ioe)
        {
            ioe.printStackTrace();  
        }
    }
}
