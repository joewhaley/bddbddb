// ConstantProp.java, created Jul 3, 2004 1:27:17 PM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb.dataflow;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.ir.Operation;
import org.sf.bddbddb.ir.OperationVisitor;
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
import org.sf.bddbddb.util.Assert;
import org.sf.bddbddb.util.Pair;
import org.sf.javabdd.BDDFactory;

/**
 * ConstantProp
 * 
 * @author John Whaley
 * @version $Id$
 */
public class ConstantProp extends RelationProblem {
    boolean TRACE = false;
    final ConstantPropFact ZERO;
    final ConstantPropFact BOTTOM;
    Map factMap;
    public ConstantPropFacts currentFacts;
    Relation currentRelation;
    IterationList currentLocation;

    public boolean direction() {
        return true;
    }

    public ConstantProp() {
        factMap = new HashMap();
        ZERO = new ConstantPropFact();
        BOTTOM = new ConstantPropFact();
    }

    public Fact getBoundary() {
        return new ConstantPropFacts();
    }

    ConstantPropFact getRepresentativeFact(Relation r, Operation op) {
        ConstantPropFact f = (ConstantPropFact) currentFacts.getFact(r);
        if (f == null) return allocNewRelation(r, op);
        return f.getRepresentative();
    }

    void changeRelationValue(Relation r, ConstantPropFact fact) {
        if (r == null) return;
        if (TRACE) System.out.println("Changing relation " + r + " to " + fact);
        ConstantPropFact old_f = (ConstantPropFact) currentFacts.getFact(r);
        if (old_f != null) {
            ConstantPropFact new_f = old_f.getRepresentative();
            if (TRACE) System.out.println("Old value of relation: " + old_f);
            if (old_f != new_f) if (TRACE) System.out
                .println("representative: " + new_f);
            fact = fact.getRepresentative();
            if (fact != new_f && old_f.backPointers != null) {
                if (TRACE) System.out
                    .println("Different fact! Replacing all copies of " + r);
                for (Iterator i = old_f.backPointers.iterator(); i.hasNext();) {
                    ConstantPropFact f = (ConstantPropFact) i.next();
                    Assert._assert(f.representative == old_f);
                    if (old_f == new_f) {
                        if (TRACE) System.out
                            .println("Relation is endpoint, using " + f
                                + " instead.");
                        new_f = f;
                    }
                    old_f.backPointers.remove(f);
                    f.representative = new_f;
                    new_f.backPointers.add(f);
                }
            }
        }
        currentFacts.relationFacts.put(r, fact);
    }

    ConstantPropFact allocNewRelation(Relation r, Object op) {
        Object key = new Pair(r, op);
        ConstantPropFact f = (ConstantPropFact) factMap.get(key);
        if (f == null) {
            factMap.put(key, f = new ConstantPropFact(r, op));
            if (TRACE) System.out.println("Allocating fact for " + key + ": "
                + f);
        }
        return f;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.dataflow.Problem#getTransferFunction(org.sf.bddbddb.ir.Operation)
     */
    public TransferFunction getTransferFunction(Operation op) {
        return new ConstantPropTF(op);
    }

    boolean isSame(ConstantPropFact f1, ConstantPropFact f2) {
        return f1 != BOTTOM && f1.equals(f2);
    }
    public class ConstantPropTF extends TransferFunction implements OperationVisitor {
        Operation op;

        public ConstantPropTF(Operation op) {
            this.op = op;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.TransferFunction#apply(org.sf.bddbddb.dataflow.Problem.Fact)
         */
        public Fact apply(Fact f) {
            currentFacts = (ConstantPropFacts) f;
            ConstantPropFact result = (ConstantPropFact) op.visit(this);
            changeRelationValue(op.getDest(), result);
            return currentFacts;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Join)
         */
        public Object visit(Join op) {
            List srcs = op.getSrcs();
            Relation r1 = (Relation) srcs.get(0);
            Relation r2 = (Relation) srcs.get(1);
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (f1 == ZERO || f2 == ZERO) return ZERO;
            if (isSame(f1, f2)) return f1;
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Project)
         */
        public Object visit(Project op) {
            List srcs = op.getSrcs();
            Relation r1 = (Relation) srcs.get(0);
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            if (f1 == ZERO) return ZERO;
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Rename)
         */
        public Object visit(Rename op) {
            List srcs = op.getSrcs();
            Relation r1 = (Relation) srcs.get(0);
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            if (f1 == ZERO) return ZERO;
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Union)
         */
        public Object visit(Union op) {
            List srcs = op.getSrcs();
            Relation r1 = (Relation) srcs.get(0);
            Relation r2 = (Relation) srcs.get(1);
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (f1 == ZERO) return f2;
            if (f2 == ZERO) return f1;
            if (isSame(f1, f2)) return f1;
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Difference)
         */
        public Object visit(Difference op) {
            List srcs = op.getSrcs();
            Relation r1 = (Relation) srcs.get(0);
            Relation r2 = (Relation) srcs.get(1);
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (f1 == ZERO) return ZERO;
            if (f2 == ZERO) return f1;
            if (isSame(f1, f2)) return ZERO;
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.JoinConstant)
         */
        public Object visit(JoinConstant op) {
            List srcs = op.getSrcs();
            Relation r1 = (Relation) srcs.get(0);
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            if (f1 == ZERO) return ZERO;
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.GenConstant)
         */
        public Object visit(GenConstant op) {
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Free)
         */
        public Object visit(Free op) {
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Universe)
         */
        public Object visit(Universe op) {
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Zero)
         */
        public Object visit(Zero op) {
            return ZERO;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Invert)
         */
        public Object visit(Invert op) {
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Copy)
         */
        public Object visit(Copy op) {
            List srcs = op.getSrcs();
            Relation r1 = (Relation) srcs.get(0);
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            return f1;
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Load)
         */
        public Object visit(Load op) {
            return allocNewRelation(op.getDest(), op);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.ir.HighLevelOperationVisitor#visit(org.sf.bddbddb.ir.Save)
         */
        public Object visit(Save op) {
            return null;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.ApplyEx)
         */
        public Object visit(ApplyEx op) {
            Relation r1 = op.getSrc1();
            Relation r2 = op.getSrc2();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (op.getOp() == BDDFactory.and) {
                if (f1 == ZERO || f2 == ZERO) return ZERO;
            } else if (op.getOp() == BDDFactory.diff) {
                if (f1 == ZERO) return ZERO;
            } else if (op.getOp() == BDDFactory.or ||
                       op.getOp() == BDDFactory.xor) {
                if (f1 == ZERO && f2 == ZERO) return ZERO;
            }
            return allocNewRelation(op.getDest(), op);
        }
    }
    public class ConstantPropFact extends RelationFact {
        Relation label;
        Object op;
        ConstantPropFact representative;
        List backPointers;

        public ConstantPropFact() {
            label = null;
            op = null;
            representative = this;
        }

        public ConstantPropFact(Relation r, Object o) {
            label = r;
            op = o;
            representative = this;
        }

        public ConstantPropFact(ConstantPropFact that) {
            label = that.label;
            op = that.op;
            representative = that.representative;
        }

        void addBackPointer(ConstantPropFact that) {
            if (backPointers == null) backPointers = new LinkedList();
            backPointers.add(that);
        }

        void removeBackPointer(ConstantPropFact that) {
            backPointers.remove(that);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#join(org.sf.bddbddb.dataflow.Problem.Fact,
         *      org.sf.bddbddb.dataflow.Problem.Fact)
         */
        public Fact join(Fact fact) {
            ConstantPropFact that = (ConstantPropFact) fact;
            if (this.equals(that)) return this;
            if (TRACE) System.out.println("Join(" + this + " != " + that + ")");
            Relation newLabel = currentRelation;
            Fact result = allocNewRelation(newLabel, currentLocation);
            if (TRACE) System.out.println("Result: " + result);
            return result;
        }

        public ConstantPropFact getRepresentative() {
            ConstantPropFact f = this;
            while (f != f.representative)
                f = f.representative;
            if (true && this.representative != f) {
                // path compression
                this.representative.removeBackPointer(this);
                this.representative = f;
                this.representative.addBackPointer(this);
            }
            return f;
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            String name;
            if (this == ZERO) name = "ZERO";
            else if (this == BOTTOM) name = "BOTTOM";
            else name = label.toString();
            sb.append(name);
            sb.append("@\"" + op + "\"");
            if (this == representative) return sb.toString();
            String rName;
            if (representative == ZERO) rName = "ZERO";
            else if (representative == BOTTOM) rName = "BOTTOM";
            else rName = representative.label.toString();
            sb.append(" (equal to ");
            sb.append(rName);
            sb.append("@\"" + representative.op + "\"");
            sb.append(")");
            return sb.toString();
        }

        public boolean equals(Object o) {
            return equals((ConstantPropFact) o);
        }

        public boolean equals(ConstantPropFact that) {
            if (this == that) return true;
            return this.getRepresentative() == that.getRepresentative();
        }

        public int hashCode() {
            //throw new InternalError("cannot use hashCode");
            return System.identityHashCode(this);
        }

        public Fact copy(IterationList loc) {
            Assert.UNREACHABLE("");
            return new ConstantPropFact(this);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.sf.bddbddb.dataflow.Problem.Fact#setLocation(org.sf.bddbddb.IterationList)
         */
        public void setLocation(IterationList loc) {
            Assert.UNREACHABLE("");
        }

        public IterationList getLocation() {
            Assert.UNREACHABLE("");
            return null;
        }
    }
    public class ConstantPropFacts extends RelationFacts {
        public RelationFacts create() {
            return new ConstantPropFacts();
        }

        public Fact join(Fact fact) {
            ConstantPropFacts that = (ConstantPropFacts) fact;
            Assert._assert(this.location == that.location, this.location
                + " != " + that.location);
            currentLocation = this.location;
            ConstantPropFacts result = (ConstantPropFacts) create();
            result.relationFacts.putAll(this.relationFacts);
            for (Iterator i = that.relationFacts.entrySet().iterator(); i
                .hasNext();) {
                Map.Entry e = (Map.Entry) i.next();
                currentRelation = (Relation) e.getKey();
                RelationFact f = (RelationFact) e.getValue();
                RelationFact old = (RelationFact) result.relationFacts.put(
                    currentRelation, f);
                if (old != null) {
                    if (TRACE) System.out.println("Joining for relation "
                        + currentRelation);
                    f = (RelationFact) f.join(old);
                    result.relationFacts.put(currentRelation, f);
                }
            }
            result.location = this.location;
            return result;
        }

        public Fact copy(IterationList loc) {
            ConstantPropFacts that = new ConstantPropFacts();
            that.relationFacts.putAll(this.relationFacts);
            that.location = loc;
            return that;
        }

        public boolean equals(RelationFacts that) {
            if (this.relationFacts == that.relationFacts) return true;
            if (relationFacts.size() != that.relationFacts.size()) {
                if (TRACE) System.out.println("Size not equal");
                return false;
            }
            Iterator i = relationFacts.entrySet().iterator();
            while (i.hasNext()) {
                Map.Entry e = (Map.Entry) i.next();
                Object key = e.getKey();
                Object value = e.getValue();
                Object value2 = that.relationFacts.get(key);
                if (!value.equals(value2)) {
                    if (TRACE) System.out.println("Key " + key + " differs: "
                        + value + " vs " + value2);
                    return false;
                }
            }
            return true;
        }

        public String toString() {
            StringBuffer sb = new StringBuffer();
            sb.append("For " + location + ":\n");
            Iterator i = relationFacts.entrySet().iterator();
            while (i.hasNext()) {
                Map.Entry e = (Map.Entry) i.next();
                Object key = e.getKey();
                Object value = e.getValue();
                sb.append(key);
                sb.append(" = ");
                sb.append(value);
                sb.append('\n');
            }
            return sb.toString();
        }
    }
    public class SimplifyVisitor implements OperationVisitor {
        public Object visit(Join op) {
            Relation r1 = op.getSrc1();
            Relation r2 = op.getSrc2();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (f1 == ZERO || f2 == ZERO) {
                return new Zero(op.getDest());
            }
            if (isSame(f1, f2)) return new Copy(op.getDest(), r1);
            return op;
        }

        public Object visit(Project op) {
            Relation r1 = op.getSrc();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            if (f1 == ZERO) {
                return new Zero(op.getDest());
            }
            return op;
        }

        public Object visit(Rename op) {
            Relation r1 = op.getSrc();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            if (f1 == ZERO) {
                return new Zero(op.getDest());
            }
            return op;
        }

        public Object visit(Union op) {
            Relation r1 = op.getSrc1();
            Relation r2 = op.getSrc2();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (f1 == ZERO) {
                if (f2 == ZERO) {
                    return new Zero(op.getDest());
                }
                return new Copy(op.getDest(), r2);
            } else {
                if (f2 == ZERO) {
                    return new Copy(op.getDest(), r1);
                }
            }
            if (isSame(f1, f2)) {
                return new Copy(op.getDest(), r1);
            }
            return op;
        }

        public Object visit(Difference op) {
            Relation r1 = op.getSrc1();
            Relation r2 = op.getSrc2();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (f1 == ZERO || isSame(f1, f2)) {
                return new Zero(op.getDest());
            }
            if (f2 == ZERO) {
                return new Copy(op.getDest(), r1);
            }
            return op;
        }

        public Object visit(JoinConstant op) {
            Relation r1 = op.getSrc();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            if (f1 == ZERO) {
                return new Zero(op.getDest());
            }
            return op;
        }

        public Object visit(GenConstant op) {
            return op;
        }

        public Object visit(Free op) {
            return op;
        }

        public Object visit(Universe op) {
            return op;
        }

        public Object visit(Zero op) {
            return op;
        }

        public Object visit(Invert op) {
            return op;
        }

        public Object visit(Copy op) {
            return op;
        }

        public Object visit(Load op) {
            return op;
        }

        public Object visit(Save op) {
            return op;
        }

        /* (non-Javadoc)
         * @see org.sf.bddbddb.ir.lowlevel.LowLevelOperationVisitor#visit(org.sf.bddbddb.ir.lowlevel.ApplyEx)
         */
        public Object visit(ApplyEx op) {
            Relation r1 = op.getSrc1();
            Relation r2 = op.getSrc2();
            ConstantPropFact f1 = getRepresentativeFact(r1, op);
            ConstantPropFact f2 = getRepresentativeFact(r2, op);
            if (op.getOp() == BDDFactory.and) {
                if (f1 == ZERO || f2 == ZERO) {
                    return new Zero(op.getDest());
                }
                if (isSame(f1, f2)) {
                    // todo: check if this gets the attributes correct.
                    return new Project(op.getDest(), r1);
                }
            } else if (op.getOp() == BDDFactory.diff) {
                if (f1 == ZERO) {
                    return new Zero(op.getDest());
                }
                if (f2 == ZERO) {
                    // todo: check if this gets the attributes correct.
                    return new Project(op.getDest(), r1);
                }
            } else if (op.getOp() == BDDFactory.or ||
                       op.getOp() == BDDFactory.xor) {
                if (f1 == ZERO) {
                    if (f2 == ZERO) {
                        return new Zero(op.getDest());
                    } else {
                        // todo: check if this gets the attributes correct.
                        return new Project(op.getDest(), op.getSrc2());
                    }
                } else if (f2 == ZERO) {
                    // todo: check if this gets the attributes correct.
                    return new Project(op.getDest(), op.getSrc1());
                }
            }
            return op;
        }
    }

    public Operation simplify(Operation op, final ConstantPropFacts facts) {
        currentFacts = facts;
        return (Operation) op.visit(new SimplifyVisitor());
    }
}