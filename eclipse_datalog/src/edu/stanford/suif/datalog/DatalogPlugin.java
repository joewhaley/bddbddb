package edu.stanford.suif.datalog;

import java.util.MissingResourceException;
import java.util.ResourceBundle;
import net.sf.bddbddb.BDDSolver;
import net.sf.bddbddb.Solver;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The main plugin class to be used in the desktop.
 */
public class DatalogPlugin extends AbstractUIPlugin {
    //The shared instance.
    private static DatalogPlugin plugin;
    //Resource bundle.
    private ResourceBundle resourceBundle;

    private Solver solver;
    
    /**
     * The constructor.
     */
    public DatalogPlugin() {
        super();
        plugin = this;
        try {
            resourceBundle = ResourceBundle
                .getBundle("edu.stanford.suif.datalog.DatalogPluginResources");
        } catch (MissingResourceException x) {
            resourceBundle = null;
        }
    }

    /**
     * This method is called upon plug-in activation
     */
    public void start(BundleContext context) throws Exception {
        super.start(context);
    }

    /**
     * This method is called when the plug-in is stopped
     */
    public void stop(BundleContext context) throws Exception {
        super.stop(context);
    }

    /**
     * Returns the shared instance.
     */
    public static DatalogPlugin getDefault() {
        return plugin;
    }

    /**
     * Returns the string from the plugin's resource bundle, or 'key' if not
     * found.
     */
    public static String getResourceString(String key) {
        ResourceBundle bundle = DatalogPlugin.getDefault().getResourceBundle();
        try {
            return (bundle != null) ? bundle.getString(key) : key;
        } catch (MissingResourceException e) {
            return key;
        }
    }

    /**
     * Returns the plugin's resource bundle,
     */
    public ResourceBundle getResourceBundle() {
        return resourceBundle;
    }

    /**
     * @return  solver
     */
    public Solver getSolver() {
        if (solver == null) {
            solver = new BDDSolver();
            try {
                solver.load("c:\\workspace\\bddbddb_examples\\pa.datalog");
            } catch (Exception x) {
                x.printStackTrace();
            }
        }
        return solver;
    }
}
