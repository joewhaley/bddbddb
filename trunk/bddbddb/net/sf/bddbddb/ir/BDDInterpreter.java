/*
 * Created on Jul 13, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package net.sf.bddbddb.ir;

import java.util.Iterator;
import net.sf.bddbddb.BDDRelation;
import net.sf.bddbddb.BDDSolver;
import net.sf.bddbddb.IterationList;
import net.sf.bddbddb.Relation;
import net.sf.javabdd.BDD;

/**
 * @author mcarbin
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class BDDInterpreter extends Interpreter {
    /**
     * @param ir
     */
    public BDDInterpreter(IR ir) {
        this.ir = ir;
        opInterpreter = new BDDOperationInterpreter((BDDSolver) ir.solver, ((BDDSolver) ir.solver).getBDDFactory());
    }

    public void interpret() {
        if (ir.DOMAIN_ASSIGNMENT)
            ((BDDOperationInterpreter)opInterpreter).needsDomainMatch = false;
        interpret(ir.graph.getIterationList());
    }

    public boolean interpret(IterationList list) {
        boolean everChanged = false;
        boolean change;
        for (;;) {
            change = false;
            for (Iterator i = list.iterator(); i.hasNext();) {
                Object o = i.next();
                if (TRACE) System.out.println(o);
                if (o instanceof IterationList) {
                    IterationList sublist = (IterationList) o;
                    if (interpret(sublist)) {
                        change = true;
                    }
                } else {
                    Operation op = (Operation) o;
                    BDDRelation dest = (BDDRelation) op.getRelationDest();
                    BDD oldValue = null;
                    Relation changed = null;
                    if (!change && dest != null && dest.getBDD() != null) {
                        oldValue = dest.getBDD().id();
                        changed = dest;
                    }
                    op.visit(opInterpreter);
                    if (oldValue != null) {
                        change = !oldValue.equals(dest.getBDD());
                        if (TRACE && change) System.out.println(changed + " Changed!");
                        oldValue.free();
                    }
                }
            }
            if (!change) break;
            everChanged = true;
            if (!list.isLoop()) break;
            interpret(list.getLoopEdge());
        }
        return everChanged;
    }
}