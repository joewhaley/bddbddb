package org.sf.bddbddb.eclipse.actions;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.io.IOException;
import org.eclipse.core.internal.resources.File;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.IClasspathContainer;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.jdt.internal.core.PackageFragment;
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
            HashSet classes = new HashSet(); // no dups
            HashSet libs = new HashSet();    // no dups            
            IStructuredSelection is = (IStructuredSelection) selection;
            IPath path = null;
            for (Iterator i = is.iterator(); i.hasNext();) {
                Object elem = i.next();
                if (elem instanceof File) continue;
                try {
                    IJavaElement o = (IJavaElement)elem;
                    System.out.println("Selected: "+o.toString().split("\n", 2)[0]);
                    if (o instanceof ICompilationUnit) {
                        classes.add(o);
                    }
                    else if (o instanceof IClassFile) {
                        libs.add(o);
                    }
                    else if (o instanceof IJavaProject){
                        IPackageFragment[] pf = ((IJavaProject) o).getPackageFragments();
                        for (int j = 0; j < pf.length; j++) {
                            //System.out.println(j + " " + pf[j]);
                            addPackageFragment(classes, libs, pf[j]);
                        }
                    }
                    /*else if (o instanceof IMember){
                        classes.add(((IMember) o).getCompilationUnit());
                    }*/
                    else if (o instanceof IPackageFragment) {
                        addPackageFragment(classes, libs, (IPackageFragment)o);
                    }
                    else {
                        MessageDialog.openInformation(window.getShell(),
                            "bddbddb Eclipse Plug-in", "Type unsupported: "+ elem.getClass());   
                    }

                    path = ResourcesPlugin.getWorkspace().getRoot().getLocation();
                    path = path.append(o.getJavaProject().getOutputLocation());
                    path = path.makeAbsolute();

                } catch (JavaModelException x) {
                    // todo!
                    System.err.println(x);
                    x.printStackTrace();
                } catch (ClassCastException x) {
                    MessageDialog.openInformation(window.getShell(),
                        "bddbddb Eclipse Plug-in", "Type unsupported: "+ elem.getClass());              
                }
            }
            System.out.println("Dumping to path: \""+path+"\"");
            if (path != null)
                System.setProperty("pas.dumppath", path.toOSString());
            PAFromSource pa = new PAFromSource();
            try {
                pa.run(classes, libs);
            } catch (IOException x) {
                MessageDialog.openInformation(window.getShell(),
                    "bddbddb Eclipse Plug-in", "IO Exception occurred! "+x.toString());
            }
        } else {
            MessageDialog.openInformation(window.getShell(),
                "bddbddb Eclipse Plug-in", "Nothing is selected!");
        }
    }

    private void addPackageFragment(HashSet classes, HashSet libs, 
        IPackageFragment pf) 
        throws JavaModelException {
        ICompilationUnit[] cu = pf.getCompilationUnits();
        IClassFile[] cf =  pf.getClassFiles();
        //System.out.println(cu.length + ", " + cf.length);
        classes.addAll(Arrays.asList(cu));
        libs.addAll(Arrays.asList(cf));
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