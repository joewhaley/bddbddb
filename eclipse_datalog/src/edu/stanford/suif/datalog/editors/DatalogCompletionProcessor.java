// DatalogCompletionProcessor.java, created Oct 17, 2004 2:32:05 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package edu.stanford.suif.datalog.editors;

import java.util.LinkedList;
import java.util.List;
import net.sf.bddbddb.Relation;
import net.sf.bddbddb.Solver;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;

/**
 * DatalogCompletionProcessor
 * 
 * @author jwhaley
 * @version $Id$
 */
public class DatalogCompletionProcessor implements IContentAssistProcessor {
    
    Solver solver;
    
    private static String getLastWord(IDocument doc, int documentOffset) {
        // Use string buffer to collect characters
        StringBuffer buf = new StringBuffer();
        for (;;) {
            try {
                // Read character backwards
                char c = doc.getChar(--documentOffset);
                if (c == ',' || c == ')' || c == '(' || c == '-' || c == '>' ||
                    Character.isWhitespace(c)) break;
                buf.append(c);
            } catch (BadLocationException e) {
                // Document start reached
            }
        }
        return buf.reverse().toString();
    }
    
    private Relation getRelation(IDocument doc, int documentOffset) {
        for (;;) {
            try {
                // Read character backwards
                char c = doc.getChar(--documentOffset);
                if (c == ')') return null;
                if (c == '(') break;
            } catch (BadLocationException e) {
                // Document start reached, no tag found
                return null;
            }
        }
        String relName = getLastWord(doc, documentOffset);
        return solver.getRelation(relName);
    }
    
    String[] myProposals = { "foo", "bar", "baz", "biz", "buz" };
    
    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeCompletionProposals(org.eclipse.jface.text.ITextViewer, int)
     */
    public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer, int offset) {
        IDocument doc = viewer.getDocument();
        String lastWord = getLastWord(doc, offset);
        List list = new LinkedList();
        for (int i = 0; i < myProposals.length; ++i) {
            if (myProposals[i].startsWith(lastWord)) {
                list.add(new CompletionProposal(myProposals[i], offset, 0, myProposals[i].length()));
            }
        }
        return (ICompletionProposal[]) list.toArray(new ICompletionProposal[list.size()]);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeContextInformation(org.eclipse.jface.text.ITextViewer, int)
     */
    public IContextInformation[] computeContextInformation(ITextViewer viewer, int offset) {
        // TODO Auto-generated method stub
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getCompletionProposalAutoActivationCharacters()
     */
    public char[] getCompletionProposalAutoActivationCharacters() {
        return new char[] { '(' };
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationAutoActivationCharacters()
     */
    public char[] getContextInformationAutoActivationCharacters() {
        // TODO Auto-generated method stub
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getErrorMessage()
     */
    public String getErrorMessage() {
        return "No proposals";
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationValidator()
     */
    public IContextInformationValidator getContextInformationValidator() {
        // TODO Auto-generated method stub
        return null;
    }
}
