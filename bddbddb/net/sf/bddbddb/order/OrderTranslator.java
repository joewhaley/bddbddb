// OrderTranslator.java, created Oct 24, 2004 12:17:57 AM by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb.order;

/**
 * Translate from one order to another.  Used when orders have different names.
 * 
 * @author jwhaley
 * @version $Id$
 */
public interface OrderTranslator {
    
    /**
     * Translate the given order.  Always generates a new Order object, even if
     * the order does not change.
     * 
     * @param o  order
     * @return  translated order
     */
    Order translate(Order o);
    
}
