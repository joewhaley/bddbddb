package org.sf.bddbddb.eclipse.actions;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.io.IOException;
import org.eclipse.core.internal.resources.File;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.InputDialog;
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
    private static String loadPath = "";
    private Set appPaths = new HashSet();
    
    /**
     * The constructor.
     */
    public GenerifyAction() {

          
    }

    private void showDialog(String s) {
        MessageDialog.openInformation(window.getShell(),
            "bddbddb Eclipse Plug-in", s);  
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
        else if (id.equals("LoadClasses")) {
            load();
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
                   
                    path = o.getJavaProject().getProject().getLocation();
                    //System.out.println("Project location: "+path);
                    path = path.makeAbsolute();
                    //System.out.println("absolute: "+path);
                    break;
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

    
    private void setAppPath() {
        String pathsep = System.getProperty("path.separator");
        StringBuffer sb = new StringBuffer();
        for (Iterator i = appPaths.iterator(); i.hasNext(); ) {
            sb.append(i.next());
            sb.append(pathsep);
        }
        System.out.println("apppath="+sb.toString());
        System.setProperty("pas.apppath", sb.toString());
    }
    
    private void load() {
        if (loadPath.equals("")) {
            InputDialog id = new InputDialog(window.getShell(),
                "bddbddb Eclipse Plug-in", "Enter load path", loadPath, null);  
            id.setBlockOnOpen(true);
            do {
                id.open();  
            } while (id.getReturnCode() == InputDialog.CANCEL);
            loadPath = id.getValue();
            System.setProperty("pas.loadpath", loadPath);
        }
        
        if (selection instanceof IStructuredSelection) {          
            IStructuredSelection is = (IStructuredSelection) selection;
            
            HashSet libs = new HashSet();
            
            for (Iterator i = is.iterator(); i.hasNext();) {
                Object elem = i.next();
                if (elem instanceof File) continue;
                try {
                    IJavaElement o = (IJavaElement)elem;
                    System.out.println("Selected: "+o.toString().split("\n", 2)[0]);
                    if (o instanceof ICompilationUnit) {
                       // ignore
                    }
                    else if (o instanceof IClassFile) {
                        libs.add(o);
                        IClassFile cf = (IClassFile)o;
                        appPaths.add(cf.getParent().getResource().getLocation().makeAbsolute().toOSString());
                    }
                    else if (o instanceof IJavaProject){
                        IPackageFragment[] pf = ((IJavaProject) o).getPackageFragments();
                        for (int j = 0; j < pf.length; j++) {
                            //System.out.println(q);
                            IPath p = pf[j].getParent().getResource().getLocation().makeAbsolute();
                            appPaths.add(p.toOSString());
                            addPackageFragment(new HashSet(), libs, pf[j]);
                        }
                    }
                    else if (o instanceof IPackageFragment) {
                        //IClasspathEntry[] cp = o.getJavaProject().getPath().app
                        //for (int j = 0; j < cp.length; j++) {
                        //  System.out.println(cp[j].getPath().makeAbsolute());  
                        //}
                        //System.out.println(q);
                        IResource r = o.getParent().getResource();
                        IPath p = (r == null) ? o.getParent().getPath() : r.getLocation();
                        appPaths.add(p.makeAbsolute().toOSString());
                        addPackageFragment(new HashSet(), libs, (IPackageFragment)o);
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
            
            setAppPath();
            
            pa.loadClasses(libs);
            
        }
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
                        //IClassFile cf = (IClassFile)o;
                        //appPaths.add(cf.getParent().getPath().makeAbsolute().toOSString());
                    }
                    else if (o instanceof IJavaProject){
                        IPackageFragment[] pf = ((IJavaProject) o).getPackageFragments();
                        for (int j = 0; j < pf.length; j++) {
                            //appPaths.add(pf[j].getParent().getPath().makeAbsolute().toOSString());
                            addPackageFragment(classes, libs, pf[j]);
                        }
                    }
                    else if (o instanceof IPackageFragment) {
                        //appPaths.add(o.getParent().getPath().makeAbsolute().toOSString());
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
            
            //setAppPath();
            
            
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