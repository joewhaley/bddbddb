// IterationList.java, created Jun 30, 2004
//Copyright (C) 2004 Michael Carbin
//Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import org.sf.bddbddb.ir.Interpreter;
import org.sf.bddbddb.ir.Operation;
import org.sf.javabdd.BDD;

/**
 * IterationList
 * 
 * @author mcarbin
 * @version $Id$
 */
public class IterationList implements IterationElement {
    List /* IterationElement */elements;
    List allNestedElems = null;
    boolean isLoop = false;
    int index;
    static int blockNumber;

    public IterationList(boolean isLoop) {
        this(isLoop, new LinkedList());
    }

    public IterationList(boolean isLoop, List elems) {
        this.isLoop = isLoop;
        this.elements = elems;
        this.index = ++blockNumber;
    }

    // Return a list that has the IR for all of the loops.
    IterationList unroll() {
        List newElements = new LinkedList();
        for (Iterator i = elements.iterator(); i.hasNext();) {
            Object o = i.next();
            if (o instanceof IterationList) {
                IterationList list = (IterationList) o;
                newElements.add(list.unroll());
            } else if (isLoop) {
                InferenceRule rule = (InferenceRule) o;
                List ir = rule.generateIR();
                newElements.addAll(ir);
            }
        }
        return new IterationList(false, newElements);
    }

    void expandInLoop() {
        List newElements = new LinkedList();
        for (Iterator i = elements.iterator(); i.hasNext();) {
            Object o = i.next();
            if (o instanceof IterationList) {
                IterationList list = (IterationList) o;
                list.expandInLoop();
                newElements.add(list);
            } else {
                InferenceRule rule = (InferenceRule) o;
                List ir = rule.generateIR_incremental();
                newElements.addAll(ir);
            }
        }
        elements = newElements;
        allNestedElems = null;
    }

    public void expand(boolean unroll) {
        List newElements = new LinkedList();
        for (Iterator i = elements.iterator(); i.hasNext();) {
            Object o = i.next();
            if (o instanceof IterationList) {
                IterationList list = (IterationList) o;
                if (list.isLoop()) {
                    if (unroll) newElements.add(list.unroll());
                    list.expandInLoop();
                } else {
                    list.expand(unroll);
                }
                newElements.add(list);
            } else {
                InferenceRule rule = (InferenceRule) o;
                List ir = rule.generateIR();
                newElements.addAll(ir);
            }
        }
        elements = newElements;
        allNestedElems = null;
    }

    public void addElement(IterationElement elem) {
        elements.add(elem);
    }

    public void removeElement(IterationElement elem) {
        elements.remove(elem);
    }

    public String toString() {
        return (isLoop ? "loop" : "list") + index;
    }

    public String toString_full() {
        return (isLoop ? "(loop) " : "") + elements.toString();
    }

    public boolean contains(IterationElement elem) {
        return getAllNestedElements().contains(elem);
    }

    public boolean update() {
        boolean everChanged = false;
        boolean changed;
        do {
            changed = false;
            for (Iterator it = elements.iterator(); it.hasNext();) {
                IterationElement elem = (IterationElement) it.next();
                boolean b = elem.update();
                changed = changed ? changed : b;
                everChanged = everChanged ? everChanged : changed;
            }
        } while (changed && isLoop);
        return everChanged;
    }

    public boolean interpret(Interpreter interpret) {
        boolean everChanged = false;
        boolean change;
        for (;;) {
            change = false;
            for (Iterator i = elements.iterator(); i.hasNext();) {
                Object o = i.next();
                System.out.println(o);
                if (o instanceof IterationList) {
                    IterationList list = (IterationList) o;
                    if (list.interpret(interpret)) {
                        change = true;
                    }
                } else {
                    Operation op = (Operation) o;
                    BDDRelation dest = (BDDRelation) op.getDest();
                    BDD oldValue = null;
                    Relation changed = null;
                    if (!change && dest != null && dest.getBDD() != null) {
                        oldValue = dest.getBDD().id();
                        changed = dest;
                    }
                    op.visit(interpret);
                    if (oldValue != null) {
                        change = !oldValue.equals(dest.getBDD());
                        if (change) System.out.println(changed + " Changed!");
                        oldValue.free();
                    }
                }
            }
            if (!change) break;
            everChanged = true;
            if (!isLoop) break;
        }
        return everChanged;
    }

    public boolean isLoop() {
        return isLoop;
    }

    public ListIterator iterator() {
        return elements.listIterator();
    }

    public ListIterator reverseIterator() {
        return new ReverseIterator(elements.listIterator(elements.size()));
    }
    class ReverseIterator implements ListIterator {
        ListIterator it;

        public ReverseIterator(ListIterator it) {
            this.it = it;
        }

        public boolean hasNext() {
            return it.hasPrevious();
        }

        public Object next() {
            return it.previous();
        }

        public int nextIndex() {
            return it.previousIndex();
        }

        public boolean hasPrevious() {
            return it.hasNext();
        }

        public Object previous() {
            return it.next();
        }

        public int previousIndex() {
            return it.nextIndex();
        }

        public void remove() {
            it.remove();
        }

        public void add(Object o) {
            throw new UnsupportedOperationException();
            //it.add(o);
        }

        public void set(Object o) {
            it.set(o);
        }
    }

    public List getAllNestedElements() {
        if (allNestedElems == null) {
            List list = new LinkedList();
            for (Iterator it = elements.iterator(); it.hasNext();) {
                Object elem = it.next();
                if (elem instanceof IterationList) {
                    list.addAll(((IterationList) elem).getAllNestedElements());
                } else {
                    list.add(elem);
                }
            }
            allNestedElems = list;
        }
        return allNestedElems;
    }
}