package org.sf.bddbddb.eclipse.actions;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.io.IOException;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.sf.bddbddb.PAFromSource;

/**
 * Our sample action implements workbench action delegate. The action proxy will
 * be created by the workbench and shown in the UI. When the user tries to use
 * the action, this delegate will be created and execution will be delegated to
 * it.
 * 
 * @see IWorkbenchWindowActionDelegate
 */
public class GenRelationsAction implements IWorkbenchWindowActionDelegate {
    private IWorkbenchWindow window;
    private ISelection selection;

    /**
     * The constructor.
     */
    public GenRelationsAction() {
    }

    /**
     * The action has been activated. The argument of the method represents the
     * 'real' action sitting in the workbench UI.
     * 
     * @see IWorkbenchWindowActionDelegate#run
     */
    public void run(IAction action) {
        if (selection instanceof IStructuredSelection && !selection.isEmpty()) {
            List classes = new LinkedList();
            IStructuredSelection is = (IStructuredSelection) selection;
            IPath path = null;
            for (Iterator i = is.iterator(); i.hasNext();) {
                Object o = i.next();
                System.out.println("Selected: "+o);
                IMember m = (IMember) o;
                ICompilationUnit cu = m.getCompilationUnit();
                classes.add(cu);
                try {
                    path = ResourcesPlugin.getWorkspace().getRoot().getLocation();
                    path = path.append(cu.getJavaProject().getOutputLocation());
                    path = path.makeAbsolute();
                } catch (JavaModelException x) {
                    // todo!
                    System.err.println(x);
                    x.printStackTrace();
                }
            }
            System.out.println("Dumping to path: \""+path+"\"");
            if (path != null)
                System.setProperty("pas.dumppath", path.toOSString());
            PAFromSource pa = new PAFromSource();
            try {
                pa.run(classes);
            } catch (IOException x) {
                MessageDialog.openInformation(window.getShell(),
                    "bddbddb Eclipse Plug-in", "IO Exception occurred! "+x.toString());
            }
        } else {
            MessageDialog.openInformation(window.getShell(),
                "bddbddb Eclipse Plug-in", "Nothing is selected!");
        }
    }

    /**
     * Selection in the workbench has been changed. We can change the state of
     * the 'real' action here if we want, but this can only happen after the
     * delegate has been created.
     * 
     * @see IWorkbenchWindowActionDelegate#selectionChanged
     */
    public void selectionChanged(IAction action, ISelection selection) {
        this.selection = selection;
    }

    /**
     * We can use this method to dispose of any system resources we previously
     * allocated.
     * 
     * @see IWorkbenchWindowActionDelegate#dispose
     */
    public void dispose() {
    }

    /**
     * We will cache window object in order to be able to provide parent shell
     * for the message dialog.
     * 
     * @see IWorkbenchWindowActionDelegate#init
     */
    public void init(IWorkbenchWindow window) {
        this.window = window;
    }
}