// SolverGUI.java, created Jun 18, 2004 12:02:08 AM by joewhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.io.File;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JTextPane;

/**
 * SolverGUI
 * 
 * @author John Whaley
 * @version $Id$
 */
public class SolverGUI extends JFrame {
    private javax.swing.JPanel jContentPane = null;
    private JMenuBar jJMenuBar = null;
    private JMenu jFileMenu = null;
    private JMenuItem jOpenMenuItem = null;
    private JMenuItem jExitMenuItem = null;
    private JFileChooser jFileChooser = null; //  @jve:decl-index=0:visual-constraint="334,13"
    private JTextPane jTextPane = null;
    private JMenuItem jSaveMenuItem = null;
    private JMenuItem jSaveAsMenuItem = null;

    /**
     * This method initializes jJMenuBar
     * 
     * @return javax.swing.JMenuBar
     */
    private JMenuBar getJJMenuBar() {
        if (jJMenuBar == null) {
            jJMenuBar = new JMenuBar();
            jJMenuBar.add(getJFileMenu());
        }
        return jJMenuBar;
    }

    /**
     * This method initializes jFileMenu
     * 
     * @return javax.swing.JMenu
     */
    private JMenu getJFileMenu() {
        if (jFileMenu == null) {
            jFileMenu = new JMenu();
            jFileMenu.setText("File");
            jFileMenu.add(getJOpenMenuItem());
            jFileMenu.add(getJSaveMenuItem());
            jFileMenu.add(getJSaveAsMenuItem());
            jFileMenu.add(getJExitMenuItem());
            jFileMenu.addSeparator();
        }
        return jFileMenu;
    }

    /**
     * This method initializes jOpenMenuItem
     * 
     * @return javax.swing.JMenuItem
     */
    private JMenuItem getJOpenMenuItem() {
        if (jOpenMenuItem == null) {
            jOpenMenuItem = new JMenuItem();
            jOpenMenuItem.setText("Open Datalog...");
            jOpenMenuItem
                .addActionListener(new java.awt.event.ActionListener() {
                    public void actionPerformed(java.awt.event.ActionEvent e) {
                        JFileChooser fc = getJFileChooser();
                        int returnVal = fc.showOpenDialog(SolverGUI.this);
                        if (returnVal == JFileChooser.APPROVE_OPTION) {
                            File file = fc.getSelectedFile();
                            jTextPane.setText("Opening: " + file.getName());
                        } else {
                            jTextPane
                                .setText("Open command cancelled by user.");
                        }
                    }
                });
        }
        return jOpenMenuItem;
    }

    private static void createAndShowGUI() {
        SolverGUI t = new SolverGUI();
        t.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        t.setVisible(true);
    }

    /**
     * This method initializes jExitMenuItem
     * 
     * @return javax.swing.JMenuItem
     */
    private JMenuItem getJExitMenuItem() {
        if (jExitMenuItem == null) {
            jExitMenuItem = new JMenuItem();
            jExitMenuItem.setText("Exit");
        }
        return jExitMenuItem;
    }

    /**
     * This method initializes jFileChooser
     * 
     * @return javax.swing.JFileChooser
     */
    private JFileChooser getJFileChooser() {
        if (jFileChooser == null) {
            jFileChooser = new JFileChooser();
        }
        return jFileChooser;
    }

    /**
     * This method initializes jTextPane
     * 
     * @return javax.swing.JTextPane
     */
    private JTextPane getJTextPane() {
        if (jTextPane == null) {
            jTextPane = new JTextPane();
            jTextPane.setFont(new java.awt.Font("Times New Roman",
                java.awt.Font.ITALIC, 24));
        }
        return jTextPane;
    }

    /**
     * This method initializes jSaveMenuItem
     * 
     * @return javax.swing.JMenuItem
     */
    private JMenuItem getJSaveMenuItem() {
        if (jSaveMenuItem == null) {
            jSaveMenuItem = new JMenuItem();
            jSaveMenuItem.setText("Save");
        }
        return jSaveMenuItem;
    }

    /**
     * This method initializes jSaveAsMenuItem
     * 
     * @return javax.swing.JMenuItem
     */
    private JMenuItem getJSaveAsMenuItem() {
        if (jSaveAsMenuItem == null) {
            jSaveAsMenuItem = new JMenuItem();
            jSaveAsMenuItem.setText("Save As...");
            jSaveAsMenuItem
                .addActionListener(new java.awt.event.ActionListener() {
                    public void actionPerformed(java.awt.event.ActionEvent e) {
                        JFileChooser fc = getJFileChooser();
                        int returnVal = fc.showSaveDialog(SolverGUI.this);
                        if (returnVal == JFileChooser.APPROVE_OPTION) {
                            File file = fc.getSelectedFile();
                            jTextPane.setText("Saving: " + file.getName());
                        } else {
                            jTextPane
                                .setText("Save command cancelled by user.");
                        }
                    }
                });
        }
        return jSaveAsMenuItem;
    }

    public static void main(String[] args) {
        javax.swing.SwingUtilities.invokeLater(new Runnable() {
            public void run() {
                createAndShowGUI();
            }
        });
    }

    /**
     * This is the default constructor
     */
    public SolverGUI() {
        super();
        initialize();
    }

    /**
     * This method initializes this
     */
    private void initialize() {
        this.setTitle("bddbddb");
        this.setSize(300, 200);
        this.setJMenuBar(getJJMenuBar());
        this.setContentPane(getJContentPane());
    }

    /**
     * This method initializes jContentPane
     * 
     * @return javax.swing.JPanel
     */
    private javax.swing.JPanel getJContentPane() {
        if (jContentPane == null) {
            jContentPane = new javax.swing.JPanel();
            jContentPane.setLayout(new java.awt.BorderLayout());
            jContentPane.add(getJTextPane(), java.awt.BorderLayout.WEST);
        }
        return jContentPane;
    }
}