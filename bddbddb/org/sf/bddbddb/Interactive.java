// Interactive.java, created Jul 29, 2004 3:40:10 PM 2004 by jwhaley
// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package org.sf.bddbddb;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import org.sf.bddbddb.Solver.MyReader;

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
    
    public static void main(String[] args) throws InstantiationException, IllegalAccessException, ClassNotFoundException, IOException {
        String solverName = System.getProperty("solver", "org.sf.bddbddb.BDDSolver");
        Solver dis = (Solver) Class.forName(solverName).newInstance();
        String file = "";
        if (args.length > 0) {
            file = args[0];
        }
        dis.initializeBasedir(file);
        Interactive a = new Interactive(dis);
        if (file.length() > 0) {
            MyReader in = new MyReader(new LineNumberReader(new FileReader(file)));
            System.out.println("Reading "+file+"...");
            dis.readDatalogProgram(in);
            in.close();
        }
        if (true) {
            dis.relationsToDump.clear();
            dis.relationsToDumpTuples.clear();
            dis.relationsToDumpNegated.clear();
            dis.relationsToDumpNegatedTuples.clear();
            dis.relationsToPrintSize.clear();
            dis.relationsToPrintTuples.clear();
        }
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
                if (s.equalsIgnoreCase("solve")) {
                    changed = true;
                    solve();
                    continue;
                }
                if (s.equalsIgnoreCase("rules")) {
                    listRules();
                    continue;
                }
                if (s.equalsIgnoreCase("relations")) {
                    listRelations();
                    continue;
                }
                if (s.startsWith("deleterule")) {
                    if (s.length() <= 11) {
                        System.out.println("Usage: deleterule #{,#}");
                    } else {
                        List rules = parseRules(s.substring(11).trim());
                        if (rules != null && !rules.isEmpty()) {
                            solver.rules.removeAll(rules);
                        }
                    }
                    continue;
                }
                if (s.startsWith("save")) {
                    if (s.length() <= 5) {
                        System.out.println("Usage: save <relation>{,<relation}>");
                    } else {
                        List relations = parseRelations(s.substring(5).trim());
                        if (relations != null && !relations.isEmpty()) {
                            solver.relationsToDump.addAll(relations);
                            solve();
                            solver.relationsToDump.removeAll(relations);
                        }
                    }
                    continue;
                }
                Object result = solver.parseDatalogLine(s, in);
                if (result != null) {
                    changed = true;
                    if (s.indexOf('?') >= 0 && result instanceof Collection) {
                        // This is a query, so we should run the solver.
                        Collection queries = (Collection) result;
                        solve();
                        solver.rules.removeAll(queries);
                        for (Iterator i = queries.iterator(); i.hasNext(); ) {
                            InferenceRule ir = (InferenceRule) i.next();
                            solver.deleteRelation(ir.bottom.relation);
                            ir.bottom.relation.free();
                            ir.free();
                        }
                    }
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

    List parseRelations(String s) {
        List relations = new LinkedList();
        while (s.length() != 0) {
            int i = s.indexOf(',');
            String relationName;
            if (i == -1) relationName = s;
            else relationName = s.substring(0, i);
            Relation r = solver.getRelation(relationName);
            if (r == null) {
                System.out.println("Unknown relation \""+relationName+"\"");
                return null;
            }
            relations.add(r);
            if (i == -1) break;
            s = s.substring(i+1).trim();
        }
        return relations;
    }
    
    void listRules() {
        int k = 0;
        for (Iterator i = solver.rules.iterator(); i.hasNext(); ) {
            InferenceRule r = (InferenceRule) i.next();
            ++k;
            System.out.println(k+": "+r);
        }
    }
    
    void listRelations() {
        System.out.println(solver.nameToRelation.keySet());
    }
    
    List parseRules(String s) {
        String ruleNum = null;
        try {
            List rules = new LinkedList();
            for (;;) {
                int i = s.indexOf(',');
                if (i == -1) ruleNum = s;
                else ruleNum = s.substring(0, i);
                int k = Integer.parseInt(ruleNum);
                if (k < 1 || k > solver.rules.size()) {
                    System.out.println("Rule number out of range: "+k);
                    return null;
                }
                rules.add(solver.rules.get(k-1));
                if (i == -1) break;
                s = s.substring(i+1).trim();
            }
            return rules;
        } catch (NumberFormatException x) {
            System.out.println("Not a number: \""+ruleNum+"\"");
        }
        return null;
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
