/*
 * Created on Jun 30, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb;

import java.util.List;
import java.util.LinkedList;
import java.util.Iterator;

;
/**
 * @author mcarbin
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class IterationList implements IterationElement {
    List /* IterationElement */elements;
    List allNestedElems = null;
    boolean isLoop = false;

    public IterationList(boolean isLoop) {
        this.isLoop = isLoop;
        elements = new LinkedList();
    }

    public void addElement(IterationElement elem) {
        elements.add(elem);
    }

    public void removeElement(IterationElement elem) {
        elements.remove(elem);
    }

    public String toString() {
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

    public boolean isLoop() {
        return isLoop;
    }

    public Iterator iterator() {
        return elements.iterator();
    }

    public List getAllNestedElements() {
        if (allNestedElems == null) {
            List list = new LinkedList();
            for (Iterator it = elements.iterator(); it.hasNext();) {
                IterationElement elem = (IterationElement) it.next();
                if (elem instanceof InferenceRule) {
                    list.add(elem);
                } else {
                    list.addAll(((IterationList) elem).getAllNestedElements());
                }
            }
            allNestedElems = list;
        }
        return allNestedElems;
    }
}