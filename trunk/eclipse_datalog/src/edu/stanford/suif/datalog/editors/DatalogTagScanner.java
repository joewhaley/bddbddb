// DatalogTagScanner.java, created Oct 17, 2004 1:57:22 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package edu.stanford.suif.datalog.editors;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

/**
 * DatalogTagScanner
 * 
 * @author jwhaley
 * @version $Id$
 */
public class DatalogTagScanner extends RuleBasedScanner
implements DatalogColorConstants {
    
    IToken domainToken;
    IToken relationToken;
    IToken headToken;
    IToken subgoalToken;
    IToken directiveToken;
    IToken commentToken;
    IToken stringToken;
    
    public DatalogTagScanner(ColorManager cm) {
        domainToken = new Token(new TextAttribute(cm.getColor(DOMAIN)));
        relationToken = new Token(new TextAttribute(cm.getColor(RELATION)));
        headToken = new Token(new TextAttribute(cm.getColor(HEAD)));
        subgoalToken = new Token(new TextAttribute(cm.getColor(SUBGOAL)));
        directiveToken = new Token(new TextAttribute(cm.getColor(DIRECTIVE)));
        commentToken = new Token(new TextAttribute(cm.getColor(COMMENT)));
        stringToken = new Token(new TextAttribute(cm.getColor(STRING)));
        
        IRule[] rules = new IRule[] {
            //new SingleLineRule("<myTag", "myTag>", tagToken, '\\', true, true),
            new SingleLineRule("\"", "\"", stringToken, '\\'),
            new EndOfLineRule("#", commentToken)
        };
        setRules(rules);
    }
    
}
