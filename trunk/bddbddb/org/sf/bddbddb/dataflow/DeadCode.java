/*
 * Created on Jul 11, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.dataflow;

import java.util.ListIterator;
import org.sf.bddbddb.IterationList;
import org.sf.bddbddb.Relation;
import org.sf.bddbddb.dataflow.Liveness.LivenessFact;
import org.sf.bddbddb.ir.IR;
import org.sf.bddbddb.ir.Operation;

/**
 * @author Administrator
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class DeadCode implements IRPass {
    public boolean TRACE = true;
    IR ir;
    Liveness liveness;

    public DeadCode(IR ir) {
        this.ir = ir;
        liveness = new Liveness(ir);
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sf.bddbddb.dataflow.IRPass#run()
     */
    public boolean run() {
        System.out.print("Running DeadCode...");
        long time = System.currentTimeMillis();
        IterationList list = ir.graph.getIterationList();
        DataflowSolver solver = new DataflowSolver();
        solver.solve(liveness, list);
        boolean result = deadCodeElimination(list);
        System.out.println(((System.currentTimeMillis()-time)/1000.)+"s");
        return result;
    }

    boolean deadCodeElimination(IterationList list) {
        boolean changed = false;
        for (ListIterator it = list.iterator(); it.hasNext();) {
            Object o = it.next();
            if (o instanceof Operation) {
                Operation op = (Operation) o;
                Relation dest = op.getRelationDest();
                if (dest != null) {
                    LivenessFact fact = liveness.getOut(op);
                    if (!fact.isAlive(dest)) {
                        if (TRACE) System.out.println(dest + " is dead after " + op + " , removing operation");
                        it.remove();
                        changed = true;
                    }
                }
            } else {
                boolean b = deadCodeElimination((IterationList) o);
                if (!changed) changed = b;
            }
        }
        return changed;
    }
}