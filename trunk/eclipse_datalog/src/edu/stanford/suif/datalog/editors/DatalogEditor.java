package edu.stanford.suif.datalog.editors;

import org.eclipse.ui.editors.text.TextEditor;

public class DatalogEditor extends TextEditor {
    private ColorManager colorManager;

    public DatalogEditor() {
        super();
        colorManager = new ColorManager();
        setSourceViewerConfiguration(new DatalogViewerConfiguration(colorManager));
        //setDocumentProvider(new XMLDocumentProvider());
    }

    public void dispose() {
        colorManager.dispose();
        super.dispose();
    }
}
