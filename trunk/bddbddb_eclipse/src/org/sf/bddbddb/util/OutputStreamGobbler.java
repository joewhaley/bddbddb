/*
 * Created on Jul 14, 2004
 */
package org.sf.bddbddb.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

/**
 * @author jzhuang
 */

public class OutputStreamGobbler extends Thread
{
    OutputStream os;
    InputStream in;
    
    
    public OutputStreamGobbler(OutputStream os)
    {
       this(os, System.in);
    }
    
    public OutputStreamGobbler(OutputStream os, InputStream o)
    {
        this.os = os;
        in = o;
    }
    
    public void run()
    {
        try
        {
            InputStreamReader isr = new InputStreamReader(in);
            BufferedReader br = new BufferedReader(isr);
            String line=null;
            OutputStreamWriter osw = new OutputStreamWriter(os);
            while ( (line = br.readLine()) != null) {
                osw.write(line);  
                osw.write('\n');
            }
            br.close();
            osw.close();
            
        } catch (IOException ioe)
        {
            ioe.printStackTrace();  
        }
    }
}
