package org.sf.bddbddb.eclipse.actions;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.io.IOException;
import org.eclipse.core.internal.resources.File;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.sf.bddbddb.PAFromSource;
import org.sf.bddbddb.SourceTransformation;

/**
 * Our sample action implements workbench action delegate. The action proxy will
 * be created by the workbench and shown in the UI. When the user tries to use
 * the action, this delegate will be created and execution will be delegated to
 * it.
 * 
 * @see IWorkbenchWindowActionDelegate
 */
public class GenerifyAction implements IWorkbenchWindowActionDelegate {
    private IWorkbenchWindow window;
    private ISelection selection;
    static private PAFromSource pa = new PAFromSource();
    

    /**
     * The constructor.
     */
    public GenerifyAction() {
        
    }

    /**
     * The action has been activated. The argument of the method represents the
     * 'real' action sitting in the workbench UI.
     * 
     * @see IWorkbenchWindowActionDelegate#run
     */
    public void run(IAction action) {
        String id = action.getId();
        if (id.equals("GenRelations")) {
            genRelations();
        }
        else if (id.equals("Parse")) {
            parse();
        }
        else if (id.equals("Reset")) {
            pa = new PAFromSource();
        }
        else if (id.equals("Transform")) {
            SourceTransformation st = pa.getTransformation();
            if (st == null) {
                showDialog("Relations must be generated before the source can be transformed!");
                return;
            }
            st.test();
        }
        else {
            showDialog("Unrecognized action!");
        }
    }

    private void genRelations() {
        if (selection instanceof IStructuredSelection && !selection.isEmpty()) {
            IStructuredSelection is = (IStructuredSelection) selection;
         
            IPath path = null;
            Iterator i = is.iterator();
            while (i.hasNext()) {
                Object elem = i.next();
                if (elem instanceof File) continue;
                try {
                    IJavaElement o = (IJavaElement)elem;
                    System.out.println("Selected: "+o.toString().split("\n", 2)[0]);
                   
                    path = ResourcesPlugin.getWorkspace().getRoot().getLocation();
                    path = path.append(o.getJavaProject().getOutputLocation());
                    path = path.makeAbsolute();
                    break;
                } catch (JavaModelException x) {
                    System.err.println(x);
                    x.printStackTrace();
                } catch (ClassCastException x) {
                    showDialog("Type unsupported: "+ elem.getClass());              
                }
            }

            System.out.println("Dumping to path: \""+path+"\"");
            if (path != null)
                System.setProperty("pas.dumppath", path.toOSString());

            try {
                pa.run();
            } catch (IOException x) {
                showDialog("IO Exception occurred! "+x.toString());
            }
        }
        else {
            showDialog("Need selection to determine dump path.");
            
        }
    }

    private void showDialog(String s) {
        MessageDialog.openInformation(window.getShell(),
            "bddbddb Eclipse Plug-in", s);  
    }
    
    private void parse() {
        if (selection instanceof IStructuredSelection && !selection.isEmpty()) {          
            IStructuredSelection is = (IStructuredSelection) selection;
            
            HashSet classes = new HashSet(), libs = new HashSet();
            
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
                            addPackageFragment(classes, libs, pf[j]);
                        }
                    }
                    else if (o instanceof IPackageFragment) {
                        addPackageFragment(classes, libs, (IPackageFragment)o);
                    }
                    else {
                        showDialog("Type unsupported: "+ elem.getClass());
                    }
                } catch (JavaModelException x) {
                    // todo!
                    System.err.println(x);
                    x.printStackTrace();
                } catch (ClassCastException x) {
                    showDialog("Type unsupported: "+ elem.getClass());
                }
            }
            pa.parse(classes, libs);
            
        } else {
            showDialog("Nothing is selected!");
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