// TryDomainOrders.java, created Oct 11, 2005 11:33:56 PM by joewhaley
// Copyright (C) 2005 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.StringTokenizer;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.math.BigInteger;
import jwutil.collections.EntryValueComparator;
import jwutil.io.SystemProperties;
import net.sf.bddbddb.order.Order;
import net.sf.bddbddb.order.OrderConstraint;
import net.sf.bddbddb.order.OrderConstraintSet;
import net.sf.bddbddb.order.OrderIterator;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.FindBestOrder;

public class TryDomainOrders {

    BDDSolver solver;
    List domList;
    String varorder;
    OrderConstraintSet loaded_varorder;
    
    public TryDomainOrders() {
        solver = new BDDSolver();
        domList = new ArrayList();
        varorder = solver.VARORDER;
        loaded_varorder = new OrderConstraintSet();
    }
    
    BDDRelation parseRelation(String name, BufferedReader in) throws IOException {
        String s = in.readLine();
        if (!s.startsWith("# ")) {
            // TODO: No header line!
            throw new IOException("no header line");
        }
        StringTokenizer st = new StringTokenizer(s.substring(2));
        List attribs = new LinkedList();
        List bdddoms = new LinkedList();
        while (st.hasMoreTokens()) {
            String msg = null;
            String dname = st.nextToken(": ");
            int dbits = Integer.parseInt(st.nextToken());
            String fdname = dname;
            while (fdname.length() > 0 &&
                   Character.isDigit(fdname.charAt(fdname.length()-1))) {
                fdname = fdname.substring(0, fdname.length()-1);
            }
            Domain fd = solver.getDomain(fdname);
            if (fd == null) {
                fd = new Domain(fdname, BigInteger.ONE.shiftLeft(dbits).subtract(BigInteger.ONE));
                solver.nameToDomain.put(fdname, fd);
            } else {
                if (dbits != fd.getSize().bitLength())
                    throw new IOException("different number of bits for "+fd+" ("+dbits+" vs "+
                                          fd.getSize().bitLength()+")");
            }
            BDDDomain d = solver.getBDDDomain(dname);
            while (d == null) {
                BDDDomain dom = solver.allocateBDDDomain(fd);
                if (dom.getName().equals(dname)) {
                    d = dom;
                    domList.add(dom);
                    break;
                }
            }
            bdddoms.add(d);
            Attribute a = new Attribute(dname, fd, dname);
            attribs.add(a);
        }
        Relation r = solver.createRelation(name, attribs);
        solver.out.println("Relation "+r+": "+attribs);
        
        // Load domain lines to figure out variable order.
        int[][] domvars = new int[bdddoms.size()][];
        int k = 0;
        for (Iterator i = bdddoms.iterator(); i.hasNext(); ++k) {
            BDDDomain d = (BDDDomain) i.next();
            s = in.readLine();
            if (!s.startsWith("# "))
                throw new IOException("missing variable line for domain "+d);
            s = s.substring(2);
            domvars[k] = new int[d.varNum()];
            st = new StringTokenizer(s);
            for (int j = 0; j < domvars[k].length; ++j) {
                if (!st.hasMoreTokens())
                    throw new IOException("not enough variables for domain "+d);
                domvars[k][j] = Integer.parseInt(st.nextToken());
            }
            if (st.hasMoreTokens()) 
                throw new IOException("too many variables for domain "+d);
        }
        // node num and var num
        s = in.readLine();
        st = new StringTokenizer(s);
        int nNodes = Integer.parseInt(st.nextToken());
        int nVars = Integer.parseInt(st.nextToken());
        // variable order line
        s = in.readLine();
        st = new StringTokenizer(s);
        int[] varorder = new int[nVars];
        for (k = 0; k < varorder.length; ++k) {
            if (!st.hasMoreTokens())
                throw new IOException("varorder line too short");
            varorder[k] = Integer.parseInt(st.nextToken());
        }
        if (st.hasMoreTokens())
            throw new IOException("varorder line too long");
        
        for (int a = 0; a < domvars.length; ++a) {
            BDDDomain adom = (BDDDomain)bdddoms.get(a);
            int[] a_vars = domvars[a];
            int a1 = varorder[a_vars[0]];
            int a2 = varorder[a_vars[a_vars.length-1]];
            int a_start = Math.min(a1, a2);
            int a_end = Math.max(a1, a2);
            for (int b = a+1; b < domvars.length; ++b) {
                BDDDomain bdom = (BDDDomain)bdddoms.get(b);
                int[] b_vars = domvars[b];
                int b1 = varorder[b_vars[0]];
                int b2 = varorder[b_vars[b_vars.length-1]];
                int b_start = Math.min(b1, b2);
                int b_end = Math.max(b1, b2);
                OrderConstraint c;
                if (a_start > b_end) {
                    c = OrderConstraint.makePrecedenceConstraint(bdom, adom);
                } else if (b_start > a_end) {
                    c = OrderConstraint.makePrecedenceConstraint(adom, bdom);
                } else {
                    c = OrderConstraint.makeInterleaveConstraint(adom, bdom);
                }
                solver.out.println("Order constraint: "+c);
                boolean ok = loaded_varorder.constrain(c);
                if (!ok)
                    solver.out.println("Note: order conflicts! cannot add constraint "+c);
            }
        }
        return (BDDRelation) r;
    }
    
    BDDRelation parseRelation(String filename) throws IOException {
        // Peek at header line to figure out relation attributes.
        int x = Math.max(filename.lastIndexOf('/'),
                         filename.lastIndexOf(SystemProperties.getProperty("file.separator")));
        int y = filename.lastIndexOf('.');
        if (x >= y)
            throw new IOException("bad filename: "+filename);
        String relationName = filename.substring(x+1, y);
        String suffixName = filename.substring(y+1);
        BufferedReader in = null;
        try {
            in = new BufferedReader(new FileReader(filename));
            // Parse BDD information.
            return parseRelation(relationName, in);
        } finally {
            if (in != null) try { in.close(); } catch (IOException _) { }
        }
    }
    
    void setVarOrder(OrderConstraintSet ocs) {
        if (varorder == null) {
            Order o = ocs.generateRandomOrder(domList);
            solver.VARORDER = o.toVarOrderString(null);
        } else {
            solver.VARORDER = varorder;
        }
        solver.setVariableOrdering();
    }
    
    void doApplyEx(BDDFactory.BDDOp op, BDD b1, BDD b2, BDD b3) {
        long time = System.currentTimeMillis();
        FindBestOrder fbo = new FindBestOrder(solver.BDDNODES, solver.BDDCACHE, solver.BDDNODES / 2, Long.MAX_VALUE, 5000);
        try {
            fbo.init(b1, b2, b3, op);
        } catch (IOException x) {
            solver.err.println("IO Exception occurred: " + x);
            fbo.cleanup();
            return;
        }
        solver.out.println("Time to initialize FindBestOrder: "+(System.currentTimeMillis()-time));
        
        OrderIterator i = new OrderIterator(domList);
        Map orderTimes = new HashMap();
        while (i.hasNext()) {
            Order o = i.nextOrder();
            String vOrder = o.toVarOrderString(null);
            solver.out.println("Trying order "+vOrder);
            vOrder = solver.fixVarOrder(vOrder, false);
            solver.out.println("Complete order "+vOrder);
            time = fbo.tryOrder(true, vOrder);
            time = Math.min(time, BDDInferenceRule.LONG_TIME);
            solver.out.println("Order "+o+" time: "+time+" ms");
            orderTimes.put(o, Long.valueOf(time));
        }
        fbo.cleanup();
        
        List sortedEntries = new ArrayList(orderTimes.entrySet());
        Collections.sort(sortedEntries, EntryValueComparator.INSTANCE);
        for (Iterator it = sortedEntries.iterator(); it.hasNext(); ) {
            Map.Entry e = (Map.Entry) it.next();
            Order o = (Order) e.getKey();
            Long t = (Long) e.getValue();
            solver.out.println("Order: "+o+" "+t+" ms");
        }
    }
    
    void handleCommand(String[] args) throws IOException {
        if (args.length > 1) {
            if (args[0].equals("relprod")) {
                if (args.length == 4) {
                    BDDRelation r1 = parseRelation(args[1]);
                    BDDRelation r2 = parseRelation(args[2]);
                    BDDRelation r3 = parseRelation(args[3]);
                    setVarOrder(loaded_varorder);
                    solver.initialize();
                    r1.load(args[1]);
                    r2.load(args[2]);
                    r3.load(args[3]);
                    doApplyEx(BDDFactory.and, r1.getBDD(), r2.getBDD(), r3.getBDD());
                    return;
                }
            } else if (args[0].equals("and")) {
                
            } else if (args[0].equals("or")) {
                
            }
        }
        solver.out.println("Usage: java "+TryDomainOrders.class.getName()+" relprod bdd1 bdd2 bdd3");
        solver.out.println("       java "+TryDomainOrders.class.getName()+" and bdd1 bdd2");
        solver.out.println("       java "+TryDomainOrders.class.getName()+" or bdd1 bdd2");
    }
    
    /**
     * @param args
     */
    public static void main(String[] args) throws IOException {
        TryDomainOrders dis = new TryDomainOrders();
        dis.handleCommand(args);
    }
}
