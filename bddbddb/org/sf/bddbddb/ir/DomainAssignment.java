// DomainAssignment.java, created Jul 11, 2004 2:33:35 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.ir;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import org.sf.bddbddb.Attribute;
import org.sf.bddbddb.BDDRelation;
import org.sf.bddbddb.Domain;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.Solver;
import org.sf.bddbddb.ir.dynamic.If;
import org.sf.bddbddb.ir.dynamic.Nop;
import org.sf.bddbddb.ir.highlevel.BooleanOperation;
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
import org.sf.bddbddb.ir.lowlevel.ApplyEx;
import org.sf.bddbddb.ir.lowlevel.Replace;
import org.sf.bddbddb.util.GenericMultiMap;
import org.sf.bddbddb.util.MultiMap;

/**
 * DomainAssignment
 * 
 * @author John Whaley
 * @version $Id$
 */
public abstract class DomainAssignment implements OperationVisitor {
    int SIZE = 16;
    Solver solver;
    MultiMap/* <Domain,Attribute> */domainToAttributes;
    List inserted;
    boolean TRACE = false;
    ListIterator currentBlock;

    public abstract void doAssignment();

    private void addConstraints(List loops, int loopDepth, IterationList list) {
        if (TRACE) System.out.println("Entering: " + list);
        List s;
        if (loopDepth >= loops.size()) {
            loops.add(s = new LinkedList());
        } else {
            s = (List) loops.get(loopDepth);
        }
        s.add(list);
        for (Iterator i = list.iterator(); i.hasNext();) {
            Object o = i.next();
            if (o instanceof IterationList) {
                IterationList that = (IterationList) o;
                addConstraints(loops, loopDepth + (that.isLoop() ? 1 : 0), that);
            }
        }
    }

    public void addConstraints(IterationList list) {
        // TODO: a better order to add the constraints.
        List loops = new LinkedList();
        addConstraints(loops, 0, list);
        while (!loops.isEmpty()) {
            int index = loops.size() - 1;
            List s = (List) loops.remove(index);
            if (TRACE) System.out.println("Doing loop depth " + index);
            for (Iterator j = s.iterator(); j.hasNext();) {
                list = (IterationList) j.next();
                System.out.print("Loop depth "+index+" "+list+"                \r");
                if (TRACE) System.out.println("Doing " + list);
                for (ListIterator i = list.iterator(); i.hasNext();) {
                    Object o = i.next();
                    if (o instanceof ApplyEx) {
                        Operation op = (Operation) o;
                        currentBlock = i;
                        op.visit(this);
                    }
                }
                for (ListIterator i = list.iterator(); i.hasNext();) {
                    Object o = i.next();
                    if (o instanceof Operation) {
                        if (o instanceof ApplyEx) continue;
                        Operation op = (Operation) o;
                        currentBlock = i;
                        op.visit(this);
                    }
                }
            }
        }
    }

    /**
     *  
     */
    public DomainAssignment(Solver s) {
        this.solver = s;
        domainToAttributes = new GenericMultiMap();
        this.inserted = new LinkedList();
        int totalNumber = 0;
        for (int i = 0; i < s.getNumberOfRelations(); ++i) {
            Relation r = s.getRelation(i);
            totalNumber += r.getAttributes().size();
        }
        for (int i = 0; i < s.getNumberOfRelations(); ++i) {
            Relation r = s.getRelation(i);
            int numAttribs = r.getAttributes().size();
            for (int j = 0; j < numAttribs; ++j) {
                Attribute a = r.getAttribute(j);
                domainToAttributes.add(a.getDomain(), a);
            }
        }
    }

    void initialize() {
        // Attributes of the same relation must be assigned to different
        // domains.
        for (int i = 0; i < solver.getNumberOfRelations(); ++i) {
            Relation r = solver.getRelation(i);
            System.out.print("Initializing "+i+"/"+solver.getNumberOfRelations()+": "+r+"                      \r");
            forceDifferent(r);
        }
    }

    abstract void forceDifferent(Relation r);

    abstract boolean forceEqual(Relation r1, Attribute a1, int i);

    abstract boolean forceEqual(Relation r1, Attribute a1, Relation r2, Attribute a2, boolean equal);

    void insertBefore(Operation op) {
        if (TRACE) System.out.println("Inserting before current operation: " + op);
        inserted.add(op);
        currentBlock.previous();
        currentBlock.add(op);
        currentBlock.next();
    }

    void insertAfter(Operation op) {
        if (TRACE) System.out.println("Inserting after current operation: " + op);
        inserted.add(op);
        currentBlock.add(op);
    }

    abstract Relation allocNewRelation(Relation old_r);

    Relation insertReplaceBefore(Operation op, Relation r1) {
        Relation r1_new = allocNewRelation(r1);
        Operation move = new Replace((BDDRelation) r1_new, (BDDRelation) r1);
        insertBefore(move);
        op.replaceSrc(r1, r1_new);
        r1 = r1_new;
        return r1;
    }

    Relation insertReplaceAfter(Operation op, Relation r0) {
        Relation r0_new = allocNewRelation(r0);
        Operation move = new Replace((BDDRelation) r0, (BDDRelation) r0_new);
        insertAfter(move);
        op.setRelationDest(r0_new);
        r0 = r0_new;
        return r0;
    }

    Object visitUnaryOp(Operation op, Relation r0, Relation r1) {
        if (TRACE) System.out.println("Unary op: " + op);
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a1 = (Attribute) i.next();
            if (r0.getAttributes().contains(a1)) {
                if (!forceEqual(r1, a1, r0, a1, true)) {
                    // Assignment failed, replace operation required.
                    // TODO: we have a choice whether to rename r0 or r1.
                    r1 = insertReplaceBefore(op, r1);
                    return visitUnaryOp(op, r0, r1);
                }
            }
        }
        return null;
    }

    Object visitBooleanOp(BooleanOperation op) {
        Relation r0 = op.getRelationDest();
        Relation r1 = op.getSrc1();
        Relation r2 = op.getSrc2();
        return visitBooleanOp(op, r0, r1, r2);
    }

    Object visitBooleanOp(Operation op, Relation r0, Relation r1, Relation r2) {
        if (TRACE) System.out.println("Boolean op: " + op);
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a1 = (Attribute) i.next();
            for (Iterator j = r2.getAttributes().iterator(); j.hasNext();) {
                Attribute a2 = (Attribute) j.next();
                if (a1 == a2) {
                    if (!forceEqual(r1, a1, r2, a2, true)) {
                        // Assignment failed, rename required.
                        // TODO: we have a choice whether to rename r1 or r2.
                        if (false) {
                            r1 = insertReplaceBefore(op, r1);
                        } else {
                            r2 = insertReplaceBefore(op, r2);
                        }
                        return visitBooleanOp(op, r0, r1, r2);
                    }
                } else if (a1.getDomain() == a2.getDomain()) {
                    if (!forceEqual(r1, a1, r2, a2, false)) {
                        // Assignment failed, rename required.
                        // TODO: we have a choice whether to rename r1 or r2.
                        if (false) {
                            r1 = insertReplaceBefore(op, r1);
                        } else {
                            r2 = insertReplaceBefore(op, r2);
                        }
                        return visitBooleanOp(op, r0, r1, r2);
                    }
                }
            }
        }
        for (Iterator i = r0.getAttributes().iterator(); i.hasNext();) {
            Attribute a0 = (Attribute) i.next();
            for (Iterator j = r1.getAttributes().iterator(); j.hasNext();) {
                Attribute a1 = (Attribute) j.next();
                if (a0 == a1) {
                    if (!forceEqual(r0, a0, r1, a1, true)) {
                        // Assignment failed, rename required.
                        r0 = insertReplaceAfter(op, r0);
                        return visitBooleanOp(op, r0, r1, r2);
                    }
                }
            }
            for (Iterator j = r2.getAttributes().iterator(); j.hasNext();) {
                Attribute a2 = (Attribute) j.next();
                if (a0 == a2) {
                    if (!forceEqual(r0, a0, r2, a2, true)) {
                        // Assignment failed, rename required.
                        r0 = insertReplaceAfter(op, r0);
                        return visitBooleanOp(op, r0, r1, r2);
                    }
                }
            }
        }
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Join)
     */
    public Object visit(Join op) {
        return visitBooleanOp(op);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Project)
     */
    public Object visit(Project op) {
        Relation r0 = op.getRelationDest();
        Relation r1 = op.getSrc();
        return visitUnaryOp(op, r0, r1);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Rename)
     */
    public Object visit(Rename op) {
        if (TRACE) System.out.println("Rename op: " + op);
        Relation r0 = op.getRelationDest();
        Relation r1 = op.getSrc();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a1 = (Attribute) i.next();
            Attribute a0 = (Attribute) op.getRenameMap().get(a1);
            if (a0 == null) a0 = a1;
            if (!forceEqual(r1, a1, r0, a0, true)) {
                // Assignment failed, rename required.
                // TODO: we have a choice whether to rename r0 or r1.
                r1 = insertReplaceBefore(op, r1);
                return visit(op);
            }
        }
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Union)
     */
    public Object visit(Union op) {
        return visitBooleanOp(op);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Difference)
     */
    public Object visit(Difference op) {
        return visitBooleanOp(op);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.JoinConstant)
     */
    public Object visit(JoinConstant op) {
        Relation r0 = op.getRelationDest();
        Relation r1 = op.getSrc();
        return visitUnaryOp(op, r0, r1);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.GenConstant)
     */
    public Object visit(GenConstant op) {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Free)
     */
    public Object visit(Free op) {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Universe)
     */
    public Object visit(Universe op) {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Zero)
     */
    public Object visit(Zero op) {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Invert)
     */
    public Object visit(Invert op) {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Copy)
     */
    public Object visit(Copy op) {
        Relation r0 = op.getRelationDest();
        Relation r1 = op.getSrc();
        return visitUnaryOp(op, r0, r1);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.Replace)
     */
    public Object visit(Replace op) {
        Relation r0 = op.getRelationDest();
        Relation r1 = op.getSrc();
        return visitUnaryOp(op, r0, r1);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Load)
     */
    public Object visit(Load op) {
        if (TRACE) System.out.println("Load op: " + op);
        Relation r0 = op.getRelationDest();
        for (Iterator i = r0.getAttributes().iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            String option = a.getOptions();
            if (option == null || option.length() == 0) continue;
            Domain d = a.getDomain();
            int number = Integer.parseInt(option.substring(d.toString().length()));
            if (!forceEqual(r0, a, number)) {
                // Assignment failed, rename required.
                r0 = insertReplaceAfter(op, r0);
                return visit(op);
            }
        }
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.highlevel.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.highlevel.Save)
     */
    public Object visit(Save op) {
        if (TRACE) System.out.println("Save op: " + op);
        Relation r1 = op.getSrc();
        for (Iterator i = r1.getAttributes().iterator(); i.hasNext();) {
            Attribute a = (Attribute) i.next();
            String option = a.getOptions();
            if (option == null || option.length() == 0) continue;
            Domain d = a.getDomain();
            int number = Integer.parseInt(option.substring(d.toString().length()));
            if (!forceEqual(r1, a, number)) {
                // Assignment failed, rename required.
                r1 = insertReplaceBefore(op, r1);
                return visit(op);
            }
        }
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.ApplyEx)
     */
    public Object visit(ApplyEx op) {
        Relation r0 = op.getRelationDest();
        Relation r1 = op.getSrc1();
        Relation r2 = op.getSrc2();
        return visitBooleanOp(op, r0, r1, r2);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.If)
     */
    public Object visit(If op) {
        return null;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.ir.dynamic.DynamicOperationVisitor#visit(org.sf.bddbddb.ir.dynamic.Nop)
     */
    public Object visit(Nop op) {
        return null;
    }
}