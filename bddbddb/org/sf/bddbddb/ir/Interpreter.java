/*
 * Created on Jul 13, 2004
 * 
 * TODO To change the template for this generated file go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
package org.sf.bddbddb.ir;

import java.util.Collection;
import java.util.Map;

/**
 * Interpreter
 * 
 * @author mcarbin
 *  
 */
public abstract class Interpreter {
    boolean TRACE = false;
    IR ir;
    OperationInterpreter opInterpreter;
    Map/* Relation,RelationStats */relationStats;
    Map/* IterationList,LoopStats */loopStats;

    public abstract void interpret();
    class RelationStats {
        int size;
    }
    class LoopStats {
        Collection/* Relation */inputRelations;
    }
}