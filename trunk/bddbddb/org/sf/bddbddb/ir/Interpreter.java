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
    public static class RelationStats {
        public int size;

        public RelationStats() {
            size = 0;
        }

        /**
         * @param that
         * @return
         */
        public RelationStats join(RelationStats that) {
            RelationStats result = new RelationStats();
            result.size = (this.size > that.size) ? this.size : that.size;
            return result;
        }

        public RelationStats copy() {
            RelationStats result = new RelationStats();
            result.size = this.size;
            return result;
        }

        public boolean equals(Object o) {
            if (o instanceof RelationStats) {
                return this.size == ((RelationStats) o).size;
            }
            return false;
        }

        public String toString() {
            return "size: " + Double.toString(size);
        }
    }
    public class LoopStats {
        Collection/* Relation */inputRelations;
    }
}