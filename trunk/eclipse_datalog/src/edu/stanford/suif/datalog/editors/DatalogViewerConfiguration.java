// DatalogViewerConfiguration.java, created Oct 17, 2004 1:48:52 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package edu.stanford.suif.datalog.editors;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

/**
 * DatalogViewerConfiguration
 * 
 * @author jwhaley
 * @version $Id$
 */
public class DatalogViewerConfiguration extends SourceViewerConfiguration
implements DatalogColorConstants {
    
    private ColorManager colorManager;
    private DatalogTagScanner scanner;

    public DatalogViewerConfiguration(ColorManager colorManager) {
        this.colorManager = colorManager;
    }

    public DatalogTagScanner getTagScanner() {
        if (scanner == null) {
            scanner = new DatalogTagScanner(colorManager);
            Color DEFAULT_TAG_COLOR = colorManager.getColor(new RGB(0, 0, 50));
            scanner.setDefaultReturnToken(new Token(new TextAttribute(DEFAULT_TAG_COLOR)));
        }
        return scanner;
    }
    
    public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) {
        PresentationReconciler reconciler = new PresentationReconciler();

        DefaultDamagerRepairer dr = new DefaultDamagerRepairer(getTagScanner());
        reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
        reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

        return reconciler;
    }
    
    public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {
        ContentAssistant assistant = new ContentAssistant();
        assistant.setContentAssistProcessor(
            new DatalogCompletionProcessor(),
            IDocument.DEFAULT_CONTENT_TYPE);
        assistant.enableAutoActivation(true);
        assistant.setAutoActivationDelay(500);
        assistant.setProposalPopupOrientation(IContentAssistant.PROPOSAL_OVERLAY);
        assistant.enablePrefixCompletion(true);
        return assistant;
    }
}
