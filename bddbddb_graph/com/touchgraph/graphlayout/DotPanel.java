// DotPanel.java, created Sep 3, 2004 3:38:34 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package com.touchgraph.graphlayout;

import java.util.ArrayList;
import java.util.Iterator;
import java.awt.Frame;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;

/**
 * DotPanel
 * 
 * @author jwhaley
 * @version $Id$
 */
public class DotPanel extends GLPanel {
    
    DotPanel(Reader r) {
        super();
        initialize2(r);
    }
    
    void initialize2(Reader dotReader) {
        try {
            loadDotGraph(dotReader);
        } catch (TGException tge) {
            System.err.println(tge.getMessage());
            tge.printStackTrace(System.err);
        } catch (IOException tge) {
            System.err.println(tge.getMessage());
            tge.printStackTrace(System.err);
        }
        setVisible(true);
    }
    
    public void loadDotGraph(Reader in) throws IOException, TGException {
        ArrayList nodes = new ArrayList();
        ArrayList edges = new ArrayList();
        DotParser p = new DotParser(in, nodes, edges);
        String graphName = p.parse();
        ArrayList nodes2 = new ArrayList(nodes.size());
        for (Iterator i = nodes.iterator(); i.hasNext(); ) {
            DotParser.GraphNode n = (DotParser.GraphNode) i.next();
            Node node = new Node(n.ID, n.lbl);
            //node.setType();
            //node.setLocation();
            // ...
            tgPanel.addNode(node);
            nodes2.add(node);
        }
        for (Iterator i = edges.iterator(); i.hasNext(); ) {
            DotParser.GraphEdge e = (DotParser.GraphEdge) i.next();
            Node srcN = (Node) nodes2.get(e.src);
            Node dstN = (Node) nodes2.get(e.dest);
            int tension = 10;
            Edge edge = new Edge(srcN, dstN, tension);
            //edge.setColor();
            //edge.setLength();
            //edge.setLabel();
            tgPanel.addEdge(edge);
        }
        
        Node n1 = (Node) nodes2.get(0);
        tgPanel.setLocale(n1, 2); // radius to keep
        setLocalityRadius(2); // radius to keep
        tgPanel.setSelect(n1);
        try {
            Thread.sleep(2000);
        } catch (InterruptedException ex) {
        }
        getHVScroll().slowScrollToCenter(n1);
    }
    
    /** Initialize panel, lens, and establish a random graph as a demonstration.
     */
    public void initialize() {
        buildPanel();
        buildLens();
        tgPanel.setLensSet(tgLensSet);
        addUIs();
    }

    public static void printUsage() {
        System.out.println("Usage: java "+DotPanel.class.getName()+" filename.dot");
    }
    
    public static void main(String[] args) {
        Reader reader;
        try {
            reader = new FileReader(args[0]);
        } catch (IOException x) {
            System.err.println(x.getMessage());
            x.printStackTrace(System.err);
            return;
        } catch (ArrayIndexOutOfBoundsException x) {
            printUsage();
            return;
        }
        
        final Frame frame;
        final DotPanel glPanel = new DotPanel(reader);
        frame = new Frame("TouchGraph GraphLayout");
        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                frame.remove(glPanel);
                frame.dispose();
            }
        });
        frame.add("Center", glPanel);
        frame.setSize(800, 600);
        frame.setVisible(true);
    }
}
