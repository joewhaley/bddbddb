// BDDInterpreter.java, created Jun 29, 2004 12:54:42 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.io.IOException;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.ir.highlevel.Copy;
import org.sf.bddbddb.ir.highlevel.Difference;
import org.sf.bddbddb.ir.highlevel.Free;
import org.sf.bddbddb.ir.highlevel.GenConstant;
import org.sf.bddbddb.ir.highlevel.Invert;
import org.sf.bddbddb.ir.highlevel.Join;
import org.sf.bddbddb.ir.highlevel.JoinConstant;
import org.sf.bddbddb.ir.highlevel.Load;
import org.sf.bddbddb.ir.highlevel.Project;
import org.sf.bddbddb.ir.highlevel.Rename;
import org.sf.bddbddb.ir.highlevel.Save;
import org.sf.bddbddb.ir.highlevel.Union;
import org.sf.bddbddb.ir.highlevel.Universe;
import org.sf.bddbddb.ir.highlevel.Zero;
import org.sf.bddbddb.ir.lowlevel.Relprod;
import org.sf.bddbddb.util.Assert;
import org.sf.javabdd.BDD;
import org.sf.javabdd.BDDDomain;
import org.sf.javabdd.BDDFactory;
import org.sf.javabdd.BDDPairing;

/**
 * BDDInterpreter
 * 
 * @author jwhaley
 * @version $Id$
 */
public class BDDInterpreter implements Interpreter {
    boolean TRACE = System.getProperty("traceinterpreter") != null;

    BDDFactory factory;
    
    /**
     * @param factory
     */
    public BDDInterpreter(BDDFactory factory) {
        this.factory = factory;
    }
    
    protected BDD makeDomainsMatch(BDD b, BDDRelation r1, BDDRelation r2) {
        boolean any = false;
        BDDPairing pair = factory.makePair();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            BDDDomain d1 = r1.getBDDDomain(a);
            BDDDomain d2 = r2.getBDDDomain(a);
            if (d2 == null || d1 == d2) continue;
            any = true;
            pair.set(d1, d2);
            if (TRACE) System.out.println("   Renaming " + d1 + " to " + d2);
        }
        if (any) {
            b.replaceWith(pair);
        }
        pair.reset();
        return b;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Join)
     */
    public Object visit(Join op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc1();
        BDDRelation r2 = (BDDRelation) op.getSrc2();
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        BDD b2 = makeDomainsMatch(r2.getBDD().id(), r2, r0);
        if (TRACE) System.out.println("   And " + r1 + "," + r2);
        b1.andWith(b2);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: " + b1.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Project)
     */
    public Object visit(Project op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc();
        List attributes = op.getAttributes();
        BDD b = factory.one();
        for (Iterator i = attributes.iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            BDDDomain d = r1.getBDDDomain(a);
            b.andWith(d.set());
            if (TRACE) System.out.println("   Projecting " + d);
        }
        if (TRACE) System.out.println("   Exist " + r1);
        BDD r = r1.getBDD().exist(b);
        b.free();
        BDD b1 = makeDomainsMatch(r, r1, r0);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: " + b1.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Rename)
     */
    public Object visit(Rename op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc();
        Map renames = op.getRenameMap();
        boolean any = false;
        BDDPairing pair = factory.makePair();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a1 = (Attribute) i.next();
            BDDDomain d1 = r1.getBDDDomain(a1);
            Attribute a0 = (Attribute) renames.get(a1);
            if (a0 == null) a0 = a1;
            BDDDomain d0 = r0.getBDDDomain(a0);
            Assert._assert(d0 != null);
            if (d1.equals(d0)) continue;
            any = true;
            pair.set(d1, d0);
            if (TRACE) System.out.println("   Renaming " + d1 + " to " + d0);
        }
        BDD b = r1.getBDD().id();
        if (any) {
            if (TRACE) System.out.println("   Replace " + r1);
            b.replaceWith(pair);
        }
        pair.reset();
        r0.setBDD(b);
        if (TRACE) System.out.println("   ---> Nodes: " + b.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Union)
     */
    public Object visit(Union op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc1();
        BDDRelation r2 = (BDDRelation) op.getSrc2();
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        BDD b2 = makeDomainsMatch(r2.getBDD().id(), r2, r0);
        if (TRACE) System.out.println("   Or " + r1 + "," + r2);
        b1.orWith(b2);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: " + b1.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Difference)
     */
    public Object visit(Difference op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc1();
        BDDRelation r2 = (BDDRelation) op.getSrc2();
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        BDD b2 = makeDomainsMatch(r2.getBDD().id(), r2, r0);
        if (TRACE) System.out.println("   Diff " + r1 + "," + r2);
        b1.applyWith(b2, BDDFactory.diff);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: " + b1.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.JoinConstant)
     */
    public Object visit(JoinConstant op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc();
        Attribute a = op.getAttribute();
        long value = op.getValue();
        BDD r = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        if (TRACE) System.out.println("   And " + r1 + ","
            + r0.getBDDDomain(a) + ":" + value);
        r.andWith(r0.getBDDDomain(a).ithVar(value));
        r0.setBDD(r);
        if (TRACE) System.out.println("   ---> Nodes: " + r.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.GenConstant)
     */
    public Object visit(GenConstant op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        Attribute a = op.getAttribute();
        long value = op.getValue();
        if (TRACE) System.out.println("   Ithvar " + r0.getBDDDomain(a)
            + ":" + value);
        BDD r = r0.getBDDDomain(a).ithVar(value);
        r0.setBDD(r);
        if (TRACE) System.out.println("   ---> Nodes: " + r.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Free)
     */
    public Object visit(Free op) {
        BDDRelation r = (BDDRelation) op.getSrc();
        if (TRACE) System.out.println("   Free " + r);
        r.free();
        //BDD b = factory.zero();
        //r.setBDD(b);
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Zero)
     */
    public Object visit(Zero op) {
        BDDRelation r = (BDDRelation) op.getDest();
        BDD b = factory.zero();
        if (TRACE) System.out.println("   Zero " + r);
        r.setBDD(b);
        if (TRACE) System.out.println("   ---> Nodes: " + b.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Universe)
     */
    public Object visit(Universe op) {
        BDDRelation r = (BDDRelation) op.getDest();
        BDD b = factory.one();
        for (Iterator i = r.getAttributes().iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            BDDDomain d = r.getBDDDomain(a);
            b.andWith(d.domain());
        }
        if (TRACE) System.out.println("   Domain " + r);
        r.setBDD(b);
        if (TRACE) System.out.println("   ---> Nodes: " + b.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Invert)
     */
    public Object visit(Invert op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc();
        if (TRACE) System.out.println("   Not " + r1);
        BDD r = makeDomainsMatch(r1.getBDD().not(), r1, r0);
        r0.setBDD(r);
        if (TRACE) System.out.println("   ---> Nodes: " + r.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Copy)
     */
    public Object visit(Copy op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc();
        if (TRACE) System.out.println("   Id " + r1);
        BDD r = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        r0.setBDD(r);
        if (TRACE) System.out.println("   ---> Nodes: " + r.nodeCount());
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Load)
     */
    public Object visit(Load op) {
        BDDRelation r = (BDDRelation) op.getDest();
        try {
            r.load();
        } catch (IOException x) {
        }
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.HighLevelInterpreter#visit(org.sf.bddbddb.ir.Save)
     */
    public Object visit(Save op) {
        BDDRelation r = (BDDRelation) op.getSrc();
        try {
            r.save();
        } catch (IOException x) {
        }
        return null;
    }

    /* (non-Javadoc)
     * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.Relprod)
     */
    public Object visit(Relprod op) {
        BDDRelation r0 = (BDDRelation) op.getDest();
        BDDRelation r1 = (BDDRelation) op.getSrc1();
        BDDRelation r2 = (BDDRelation) op.getSrc2();
        BDD b1 = makeDomainsMatch(r1.getBDD().id(), r1, r0);
        BDD b2 = makeDomainsMatch(r2.getBDD().id(), r2, r0);
        BDD b3 = op.getProjectSet();
        if (TRACE) System.out.println("   Relprod " + r1 + "," + r2 + "," + op.getAttributes());
        b1.andWith(b2);
        r0.setBDD(b1);
        if (TRACE) System.out.println("   ---> Nodes: " + b1.nodeCount());
        return null;
    }
}