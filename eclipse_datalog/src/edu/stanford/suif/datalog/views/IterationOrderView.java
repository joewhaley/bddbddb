package edu.stanford.suif.datalog.views;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import net.sf.bddbddb.InferenceRule;
import net.sf.bddbddb.IterationElement;
import net.sf.bddbddb.IterationFlowGraph;
import net.sf.bddbddb.IterationList;
import net.sf.bddbddb.Solver;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerDropAdapter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.dnd.ByteArrayTransfer;
import org.eclipse.swt.dnd.DND;
import org.eclipse.swt.dnd.DragSourceAdapter;
import org.eclipse.swt.dnd.DragSourceEvent;
import org.eclipse.swt.dnd.Transfer;
import org.eclipse.swt.dnd.TransferData;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.DrillDownAdapter;
import org.eclipse.ui.part.ViewPart;
import edu.stanford.suif.datalog.DatalogPlugin;

/**
 * This sample class demonstrates how to plug-in a new workbench view. The view
 * shows data obtained from the model. The sample creates a dummy model on the
 * fly, but a real implementation would connect to the model available either in
 * this or another plug-in (e.g. the workspace). The view is connected to the
 * model using a content provider.
 * <p>
 * The view uses a label provider to define how model objects should be
 * presented in the view. Each view can present the same model objects using
 * different labels and icons, if needed. Alternatively, a single label provider
 * can be shared between views in order to ensure that objects of the same type
 * are presented in the same way everywhere.
 * <p>
 */
public class IterationOrderView extends ViewPart {
    private TreeViewer viewer;
    private DrillDownAdapter drillDownAdapter;
    private Action action1;
    private Action action2;
    private Action doubleClickAction;
    
    public Solver getSolver() {
        return DatalogPlugin.getDefault().getSolver();
    }
    
    public IterationFlowGraph getIFG() {
        return DatalogPlugin.getDefault().getSolver().getIterationFlowGraph();
    }
    
    /*
     * The content provider class is responsible for providing objects to the
     * view. It can wrap existing objects in adapters or simply return objects
     * as-is. These objects may be sensitive to the current input of the view,
     * or ignore it and always show the same content (like Task List, for
     * example).
     */
    class TreeObject implements IAdaptable {
        private String name;
        private TreeParent parent;
        private IterationElement element;

        public TreeObject(String name, IterationElement element) {
            this.name = name;
            this.element = element;
        }

        private TreeObject(TreeObject that) {
            this.name = that.name;
            this.element = that.element;
        }
        
        public TreeObject copy() {
            return new TreeObject(this);
        }
        
        public String getName() {
            return name;
        }

        public IterationElement getElement() {
            return element;
        }
        
        public void setParent(TreeParent parent) {
            this.parent = parent;
        }

        public TreeParent getParent() {
            return parent;
        }

        public String toString() {
            return getName();
        }

        public Object getAdapter(Class key) {
            return null;
        }
    }
    class TreeParent extends TreeObject {
        private ArrayList children;

        public TreeParent(String name, IterationList list) {
            super(name, list);
            children = new ArrayList();
        }

        private TreeParent(TreeParent that) {
            super(that.getName(), that.getList());
            children = new ArrayList(that.children.size());
            for (Iterator i = that.children.iterator(); i.hasNext(); ) {
                TreeObject o = (TreeObject) i.next();
                addChild(o.copy());
            }
        }
        
        public TreeObject copy() {
            return new TreeParent(this);
        }
        
        public IterationList getList() {
            return (IterationList) getElement();
        }
        
        public void addChild(TreeObject child) {
            children.add(child);
            child.setParent(this);
        }

        public void addChild(int index, TreeObject child) {
            children.add(index, child);
            child.setParent(this);
        }

        public void removeChild(TreeObject child) {
            children.remove(child);
            child.setParent(null);
        }

        public int indexOf(TreeObject child) {
            return children.indexOf(child);
        }
        
        public TreeObject removeChild(int index) {
            TreeObject child = (TreeObject) children.remove(index);
            child.setParent(null);
            return child;
        }
        
        public TreeObject[] getChildren() {
            return (TreeObject[]) children.toArray(new TreeObject[children.size()]);
        }

        public Iterator iterator() {
            return children.iterator();
        }
        
        public boolean hasChildren() {
            return children.size() > 0;
        }
        
        public boolean contains(TreeObject child) {
            for (Iterator i = children.iterator(); i.hasNext(); ) {
                TreeObject o = (TreeObject) i.next();
                if (o.element.equals(child.element)) return true;
                if (o instanceof TreeParent && ((TreeParent) o).contains(child)) return true;
            }
            return false;
        }
    }
    
    public TreeObject makeTreeObject(IterationElement e) {
        if (e instanceof IterationList) {
            IterationList list = (IterationList) e;
            TreeParent p = new TreeParent(e.toString(), list);
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                IterationElement e2 = (IterationElement) i.next();
                TreeObject o = makeTreeObject(e2);
                p.addChild(o);
            }
            return p;
        } else {
            TreeObject o = new TreeObject(e.toString(), e);
            return o;
        }
    }
    
    
    class ViewContentProvider implements IStructuredContentProvider, ITreeContentProvider {
        private TreeParent invisibleRoot;

        public void inputChanged(Viewer v, Object oldInput, Object newInput) {
        }

        public void dispose() {
        }

        public Object[] getElements(Object parent) {
            if (parent.equals(getViewSite())) {
                if (invisibleRoot == null) initialize();
                return getChildren(invisibleRoot);
            }
            return getChildren(parent);
        }

        public Object getParent(Object child) {
            if (child instanceof TreeObject) {
                return ((TreeObject) child).getParent();
            }
            return null;
        }

        public Object[] getChildren(Object parent) {
            if (parent instanceof TreeParent) {
                return ((TreeParent) parent).getChildren();
            }
            return new Object[0];
        }

        public boolean hasChildren(Object parent) {
            if (parent instanceof TreeParent) return ((TreeParent) parent).hasChildren();
            return false;
        }

        private void initialize() {
            IterationList list = getIFG().getIterationList();
            invisibleRoot = (TreeParent) makeTreeObject(list);
        }
    }
    class ViewLabelProvider extends LabelProvider {
        public String getText(Object obj) {
            return obj.toString();
        }

        public Image getImage(Object obj) {
            String imageKey = ISharedImages.IMG_OBJ_ELEMENT;
            if (obj instanceof TreeParent) imageKey = ISharedImages.IMG_OBJ_FOLDER;
            return PlatformUI.getWorkbench().getSharedImages().getImage(imageKey);
        }
    }

    class DragListener extends DragSourceAdapter {
        private StructuredViewer viewer;

        DragListener(StructuredViewer v) {
            this.viewer = v;
        }

        public void dragStart(DragSourceEvent event) {
            event.doit = !viewer.getSelection().isEmpty();
        }

        public void dragSetData(DragSourceEvent event) {
            // Copy the data from this viewer.
            IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
            //if (instance.isSupportedType(event.dataType))
            {
                List selected = selection.toList();
                event.data = selected;
            }
        }

        public void dragFinished(DragSourceEvent event) {
            if (!event.doit) return;
            // if the gadget was moved, remove it from the source viewer
            if (event.detail == DND.DROP_MOVE) {
                IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
                for (Iterator it = selection.iterator(); it.hasNext(); ) {
                    TreeObject o = (TreeObject) it.next();
                    TreeParent parent = o.getParent();
                    int index = parent.indexOf(o);
                    parent.removeChild(index);
                    parent.getList().removeElement(index);
                }
                viewer.refresh();
            }
        }
    }

    class DropListener extends ViewerDropAdapter {
        DropListener(Viewer viewer) {
            super(viewer);
        }

        public boolean performDrop(Object data) {
            TreeObject target = (TreeObject) getCurrentTarget();
            if (target == null) {
                // Use the root as the target.
                target = (TreeObject) getViewer().getInput();
            }
            List toDrop = (List) data;
            TreeViewer viewer = (TreeViewer) getViewer();
            // cannot drop an element onto itself or a child
            for (Iterator i = toDrop.iterator(); i.hasNext();) {
                TreeObject e = (TreeObject) i.next();
                if (e.element.equals(target.element)) {
                    //System.out.println("Cannot drop an element on itself.");
                    return false;
                }
                if (e instanceof TreeParent && ((TreeParent) e).contains(target)) {
                    //System.out.println("Cannot drop an element onto a child.");
                    return false;
                }
            }
            TreeParent targetParent = target.getParent();
            int index = -1;
            switch (getCurrentLocation()) {
                case LOCATION_BEFORE :
                    index = targetParent.indexOf(target);
                    target = targetParent;
                    break;
                case LOCATION_AFTER :
                    index = targetParent.indexOf(target) + 1;
                    target = targetParent;
                    break;
                default :
                    break;
            }
            if (!(target instanceof TreeParent)) {
                index = targetParent.indexOf(target);
                target = targetParent;
            }
            for (Iterator i = toDrop.iterator(); i.hasNext();) {
                TreeObject e = (TreeObject) i.next();
                e = e.copy();
                TreeParent p = (TreeParent) target;
                if (index == -1) {
                    p.addChild(e);
                    p.getList().addElement(e.getElement());
                } else {
                    p.addChild(index, e);
                    p.getList().addElement(index, e.getElement());
                }
                viewer.add(p, e);
                viewer.reveal(e);
            }
            return true;
        }

        public boolean validateDrop(Object target, int operation, TransferData transferType) {
            return TRANSFER_INSTANCE.isSupportedType(transferType);
        }
    }
    
    TreeObjectTransfer TRANSFER_INSTANCE = new TreeObjectTransfer();
    private static final String TYPE_NAME = "treeobject-transfer-format";
    private static final int TYPEID = ByteArrayTransfer.registerType(TYPE_NAME);
    
    class TreeObjectTransfer extends ByteArrayTransfer {
        private TreeObjectTransfer() {
        }

        protected List/*<TreeObject>*/ fromByteArray(byte[] bytes) {
            DataInputStream in = new DataInputStream(new ByteArrayInputStream(bytes));
            try {
                int i = in.readInt();
                List result = new ArrayList(i);
                for (int j = 0; j < i; ++j) {
                    String s = in.readUTF();
                    if (s.startsWith("rule")) {
                        InferenceRule ir = getSolver().getRule(s);
                        TreeObject o = makeTreeObject(ir);
                        result.add(o);
                    } else if (s.startsWith("list") || s.startsWith("loop")) {
                        IterationList ie = (IterationList) getIFG().getIterationElement(s); 
                        TreeParent p = (TreeParent) makeTreeObject(ie);
                        result.add(p);
                    } else {
                        return null;
                    }
                }
                return result;
            } catch (IOException e) {
                return null;
            }
        }

        /*
         * Method declared on Transfer.
         */
        protected int[] getTypeIds() {
            return new int[]{TYPEID};
        }

        /*
         * Method declared on Transfer.
         */
        protected String[] getTypeNames() {
            return new String[]{TYPE_NAME};
        }

        /*
         * Method declared on Transfer.
         */
        protected void javaToNative(Object object, TransferData transferData) {
            byte[] bytes = toByteArray((List) object);
            if (bytes != null) super.javaToNative(bytes, transferData);
        }

        /*
         * Method declared on Transfer.
         */
        protected Object nativeToJava(TransferData transferData) {
            byte[] bytes = (byte[]) super.nativeToJava(transferData);
            return fromByteArray(bytes);
        }

        protected byte[] toByteArray(List/*<TreeObject>*/ elems) {
            ByteArrayOutputStream byteOut = new ByteArrayOutputStream();
            DataOutputStream out = new DataOutputStream(byteOut);
            byte[] bytes = null;
            try {
                out.writeInt(elems.size());
                for (Iterator i = elems.iterator(); i.hasNext();) {
                    TreeObject o = (TreeObject) i.next();
                    IterationElement e = o.getElement();
                    if (e instanceof InferenceRule) out.writeUTF("rule" + ((InferenceRule) e).id);
                    else out.writeUTF(e.toString());
                }
                out.close();
                bytes = byteOut.toByteArray();
            } catch (IOException e) {
                //when in doubt send nothing
            }
            return bytes;
        }
    }
    
    /**
     * The constructor.
     */
    public IterationOrderView() {
    }

    /**
     * This is a callback that will allow us to create the viewer and initialize
     * it.
     */
    public void createPartControl(Composite parent) {
        viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
        drillDownAdapter = new DrillDownAdapter(viewer);
        viewer.setContentProvider(new ViewContentProvider());
        viewer.setLabelProvider(new ViewLabelProvider());
        //viewer.setSorter(new NameSorter());
        viewer.setInput(getViewSite());
        makeActions();
        hookContextMenu();
        hookDoubleClickAction();
        contributeToActionBars();
        hookDND();
    }

    private void hookContextMenu() {
        MenuManager menuMgr = new MenuManager("#PopupMenu");
        menuMgr.setRemoveAllWhenShown(true);
        menuMgr.addMenuListener(new IMenuListener() {
            public void menuAboutToShow(IMenuManager manager) {
                IterationOrderView.this.fillContextMenu(manager);
            }
        });
        Menu menu = menuMgr.createContextMenu(viewer.getControl());
        viewer.getControl().setMenu(menu);
        getSite().registerContextMenu(menuMgr, viewer);
    }

    private void contributeToActionBars() {
        IActionBars bars = getViewSite().getActionBars();
        fillLocalPullDown(bars.getMenuManager());
        fillLocalToolBar(bars.getToolBarManager());
    }

    private void fillLocalPullDown(IMenuManager manager) {
        manager.add(action1);
        manager.add(new Separator());
        manager.add(action2);
    }

    private void fillContextMenu(IMenuManager manager) {
        manager.add(action1);
        manager.add(action2);
        manager.add(new Separator());
        drillDownAdapter.addNavigationActions(manager);
        // Other plug-ins can contribute there actions here
        manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
    }

    private void fillLocalToolBar(IToolBarManager manager) {
        manager.add(action1);
        manager.add(action2);
        manager.add(new Separator());
        drillDownAdapter.addNavigationActions(manager);
    }

    private void makeActions() {
        action1 = new Action() {
            public void run() {
                showMessage("Action 1 executed");
            }
        };
        action1.setText("Action 1");
        action1.setToolTipText("Action 1 tooltip");
        action1.setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(
            ISharedImages.IMG_OBJS_INFO_TSK));
        action2 = new Action() {
            public void run() {
                showMessage("Action 2 executed");
            }
        };
        action2.setText("Action 2");
        action2.setToolTipText("Action 2 tooltip");
        action2.setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(
            ISharedImages.IMG_OBJS_INFO_TSK));
        doubleClickAction = new Action() {
            public void run() {
                ISelection selection = viewer.getSelection();
                Object obj = ((IStructuredSelection) selection).getFirstElement();
                showMessage("Double-click detected on " + obj.toString());
            }
        };
    }

    private void hookDoubleClickAction() {
        viewer.addDoubleClickListener(new IDoubleClickListener() {
            public void doubleClick(DoubleClickEvent event) {
                doubleClickAction.run();
            }
        });
    }

    private void hookDND() {
        int ops = DND.DROP_COPY | DND.DROP_MOVE;
        Transfer[] transfers = new Transfer[] { TRANSFER_INSTANCE };
        viewer.addDragSupport(ops, transfers, new DragListener(viewer));
        viewer.addDropSupport(ops, transfers, new DropListener(viewer));
    }
    
    private void showMessage(String message) {
        MessageDialog.openInformation(viewer.getControl().getShell(), "Rule Iteration Order View",
            message);
    }

    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {
        viewer.getControl().setFocus();
    }
}
