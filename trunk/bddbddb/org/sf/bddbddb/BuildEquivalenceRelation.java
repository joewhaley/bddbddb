// BuildEquivalenceRelation.java, created Jul 30, 2004 12:46:08 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.io.BufferedReader;
import java.io.FileReader;
import org.sf.bddbddb.util.IndexMap;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;


/**
 * BuildEquivalenceRelation
 * 
 * @author jwhaley
 * @version $Id$
 */
public class BuildEquivalenceRelation {

    public static void main(String[] args) throws Exception {
        int n = args.length / 2;
        
        BDDDomain[] domains = new BDDDomain[n];
        long[] sizes = new long[n];
        BDDDomain targetDomain;
        
        BDDSolver s = new BDDSolver();
        s.readDatalogProgram(s.basedir+"fielddomains.pa");
        System.out.println("Domains: "+s.nameToDomain);
        s.loadBDDDomainInfo();
        s.setVariableOrdering();

        targetDomain = s.getBDDDomain(args[0]);
        if (targetDomain == null) throw new Exception("Invalid domain: "+args[0]);
        for (int i = 0; i < domains.length; ++i) {
            String name = args[i*2 + 1];
            domains[i] = s.getBDDDomain(name);
            if (domains[i] == null)
                throw new Exception("Invalid domain: "+args[0]);
            String size = args[i*2 + 2];
            try {
                sizes[i] = Long.parseLong(size);
            } catch (NumberFormatException x) {
                BufferedReader in = new BufferedReader(new FileReader(s.basedir+size));
                IndexMap m = IndexMap.loadStringMap("map", in);
                in.close();
                sizes[i] = m.size();
            }
        }
        
        long index = 0;
        for (int i = 0; i < domains.length; ++i) {
            int bits = Math.min(domains[i].varNum(), targetDomain.varNum());
            BDD b = domains[i].buildAdd(targetDomain, bits, index);
            b.andWith(domains[i].varRange(0, sizes[i]));
            System.out.println(domains[i]+" [0.."+sizes[i]+"] corresponds to "+targetDomain+"["+index+".."+(index+sizes[i])+"]");
            System.out.println("Result: "+b.nodeCount()+" nodes");
            s.bdd.save("map_"+domains[i]+"_"+targetDomain+".bdd", b);
            index += sizes[i] + 1;
        }
    }
    
}
