// Interactive.java, created Jul 29, 2004 3:40:10 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import org.sf.bddbddb.Solver.MyReader;
import org.sf.bddbddb.util.Assert;

/**
 * Interactive
 * 
 * @author jwhaley
 * @version $Id$
 */
public class Interactive {
    
    Solver solver;
    
    Interactive(Solver s) {
        this.solver = s;
    }
    
    public static void main(String[] args) throws InstantiationException, IllegalAccessException, ClassNotFoundException {
        String solverName = System.getProperty("solver", "org.sf.bddbddb.BDDSolver");
        Solver dis = (Solver) Class.forName(solverName).newInstance();
        dis.initializeBasedir("");
        Interactive a = new Interactive(dis);
        a.interactive();
    }
    
    static String readLine(MyReader in) throws IOException {
        String s = in.readLine();
        if (s == null) return null;
        s = s.trim();
        while (s.endsWith("\\")) {
            String s2 = in.readLine();
            if (s2 == null) break;
            s2 = s2.trim();
            s = s.substring(0, s.length() - 1) + s2;
        }
        return s;
    }
    
    boolean changed = false;
    
    List log;
    
    void dumpLog() throws IOException {
        BufferedWriter w = null;
        try {
            w = new BufferedWriter(new FileWriter("bddbddb.log"));
            for (Iterator i = log.iterator(); i.hasNext(); ) {
                w.write(i.next()+"\n");
            }
        } finally {
            if (w != null) try { w.close(); } catch (IOException _) { }
        }
    }
    
    public void interactive() {
        log = new LinkedList();
        LineNumberReader lin = new LineNumberReader(new InputStreamReader(System.in));
        MyReader in = new MyReader(lin);
        outer:
        for (;;) {
            try {
                System.out.print("> ");
                String s = readLine(in);
                if (s == null) break;
                if (s.equalsIgnoreCase("exit") || s.equalsIgnoreCase("quit")) {
                    return;
                }
                log.add(s);
                if (s.equalsIgnoreCase("dumplog")) {
                    dumpLog();
                    System.out.println("Log dumped. ("+log.size()+" lines)");
                    continue;
                }
                if (s.startsWith("save")) {
                    if (s.length() <= 5) {
                        System.out.println("Usage: save <relation>{,<relation}>");
                    } else {
                        String relationName = s.substring(5);
                        List relations = new LinkedList();
                        while (s.length() != 0) {
                            Relation r = solver.getRelation(s);
                            if (r == null) {
                                System.out.println("Unknown relation \""+s+"\"");
                                continue outer;
                            }
                            relations.add(r);
                            int i = s.indexOf(',');
                            if (i == -1) break;
                            s = s.substring(i).trim();
                        }
                        solver.relationsToDump.addAll(relations);
                        solve();
                        solver.relationsToDump.removeAll(relations);
                    }
                    continue;
                }
                boolean b = solver.parseDatalogLine(s, in);
                if (b) {
                    changed = true;
                }
                //System.out.println("Parsed successfully.");
                if (s.indexOf('?') >= 0) {
                    // This is a query, so we should run the solver.
                    InferenceRule query = (InferenceRule) solver.rules.get(solver.rules.size()-1);
                    Relation r = query.bottom.relation;
                    Assert._assert(solver.relationsToPrintTuples.contains(r));
                    solve();
                    solver.rules.remove(query);
                    solver.deleteRelation(r);
                }
            } catch (NoSuchElementException x) {
                System.out.println("Invalid command.");
                log.remove(log.size()-1);
            } catch (IllegalArgumentException x) {
                System.out.println("Invalid command.");
                log.remove(log.size()-1);
            } catch (IOException x) {
                System.out.println("IO Exception occurred: "+x);
            }
        }
    }

    Set loadedRelations = new HashSet();
    
    void solve() throws IOException {
        if (changed) {
            solver.splitRules();
            if (solver.NOISY) solver.out.print("Initializing solver: ");
            solver.initialize();
            if (solver.NOISY) solver.out.println("done.");
            if (!loadedRelations.containsAll(solver.relationsToLoad) ||
                !loadedRelations.containsAll(solver.relationsToLoadTuples)) {
                if (solver.NOISY) solver.out.print("Loading initial relations: ");
                Set newRelationsToLoad = new HashSet(solver.relationsToLoad);
                newRelationsToLoad.removeAll(loadedRelations);
                long time = System.currentTimeMillis();
                for (Iterator i = newRelationsToLoad.iterator(); i.hasNext();) {
                    Relation r = (Relation) i.next();
                    try {
                        r.load();
                    } catch (IOException x) {
                        System.out.println("WARNING: Cannot load bdd " + r + ": " + x.toString());
                    }
                }
                newRelationsToLoad = new HashSet(solver.relationsToLoadTuples);
                newRelationsToLoad.removeAll(loadedRelations);
                for (Iterator i = newRelationsToLoad.iterator(); i.hasNext();) {
                    Relation r = (Relation) i.next();
                    try {
                        r.loadTuples();
                    } catch (IOException x) {
                        System.out.println("WARNING: Cannot load tuples " + r + ": " + x.toString());
                    }
                }
                time = System.currentTimeMillis() - time;
                if (solver.NOISY) solver.out.println("done. (" + time + " ms)");
                loadedRelations.addAll(solver.relationsToLoad);
                loadedRelations.addAll(solver.relationsToLoadTuples);
            }
            if (solver.NOISY) solver.out.println("Solving: ");
            long time = System.currentTimeMillis();
            solver.solve();
            time = System.currentTimeMillis() - time;
            if (solver.NOISY) solver.out.println("done. (" + time + " ms)");
            long solveTime = time;
            changed = false;
        }
        solver.saveResults();
    }
}
