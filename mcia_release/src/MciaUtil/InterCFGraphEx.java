/**
 * File: src/McaiUtil/InterCFGraphEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 12/15/14		hcai		created; for computing, exceptional interprocedural control flow graph (ICFG)
 *							initially for SEA implementation
 *  
*/
package MciaUtil;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import dua.global.ProgramFlowGraph;
import dua.method.CFG;
import dua.method.CallSite;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.toolkits.graph.DirectedGraph;
import soot.util.dot.DotGraph;
import soot.util.dot.DotGraphAttribute;
import soot.util.dot.DotGraphConstants;
import soot.util.dot.DotGraphEdge;
import soot.util.dot.DotGraphNode;

import soot.util.Chain;
import soot.util.HashChain;

/**
 * An ICFG builder that computes interprocedural control flow graph of the given input graph covering
 * exceptional units (catch and finally blocks) for all classes and methods
 * By default, the ICFG is the collection of per-method (statement-level) CFGs connected with call edges and return edges 
 * @author hcai
 */
public class InterCFGraphEx implements DirectedGraph<Unit> {
	// all nodes that have no predecessor
    List<Unit> heads;
    // all nodes that have no successor
    List<Unit> tails;

    // the two main mappings for the graph structure
    protected Map<Unit,List<Unit>> unitToSuccs;
    protected Map<Unit,List<Unit>> unitToPreds; 
    
    // mapping from method to cfg
    protected Map<SootMethod, CompleteUnitGraphEx> mToCfg;
		
	protected boolean debugOut;
	
	public boolean modelLibfuncs = true;
	
	public InterCFGraphEx(boolean _debug) {
		
		unitToSuccs = new HashMap<Unit, List<Unit>>();
		unitToPreds = new HashMap<Unit, List<Unit>>();
		heads = new ArrayList<Unit>();
		tails = new ArrayList<Unit>();
		
		mToCfg = new HashMap<SootMethod, CompleteUnitGraphEx>();
		
		debugOut = _debug;
	}
	public InterCFGraphEx() {
		this(true);
	}
	public void turnDebug(boolean b) {
		debugOut = b;
	}
	
	public List<Unit> getHeads() {
		return heads;
	}
	public List<Unit> getTails() {
		return tails;
	}
	public int getNumberOfNodes() { 
		return unitToSuccs.keySet().size() + heads.size(); 
	}
	public int size() {
		return getNumberOfNodes();
	}
	public int getNumberOfEdges() {
		int szEdge = 0;
		for (Unit u : unitToSuccs.keySet()) {
			szEdge += unitToSuccs.get(u).size();
		}
		return szEdge;
	}
	@Override public String toString() {
		return "Exceptional Inter-CFG [Static] " + getNumberOfNodes() + " nodes, " + getNumberOfEdges() + " edges ";
	}
		
	public List<Unit> getPredsOf(Unit _node) { 
		if (_node == null) return new ArrayList<Unit>();
		return unitToPreds.get(_node);
	}
	
	public List<Unit> getSuccsOf(Unit _node) { 
		if (_node == null) return new ArrayList<Unit>();
		return unitToSuccs.get(_node);
	}
	
	public CompleteUnitGraphEx getCFG(SootMethod m) {
		return mToCfg.get(m);
	}
	
	// get the ENTRY node of the given method whose signature equals to the input query
	public Unit getStart(SootMethod query) {
		if (!mToCfg.containsKey(query)) return null; // invalid query
		return mToCfg.get(query).ENTRY;
	}
	public SootMethod getMethodByName(String f) {
		for (SootMethod m : mToCfg.keySet()) {
			if (m.getSignature().compareToIgnoreCase(f) == 0) {
				return m;
			}
		}
		return null;
	}
	
	protected void buildHeadsAndTails() {
		for (Unit n : unitToPreds.keySet()) {
			if (unitToPreds.get(n)==null || unitToPreds.get(n).size()<1) {
				heads.add(n);
			}
			if (unitToSuccs.get(n)==null || unitToSuccs.get(n).size()<1) {
				tails.add(n);
			}
		}
	}
	
	Chain<Unit> innerChain = new HashChain<Unit>();
	public Iterator<Unit> iterator() {
		if (0 == innerChain.size()) {
			innerChain.addAll(unitToSuccs.keySet());
			innerChain.addAll(getHeads());
			innerChain.addAll(getTails());
		}
		return innerChain.iterator();
	}
		
	/** phase 1: copy per-method CFG for all methods */
	private void collectCFGs() {
		/* traverse all classes */
		Iterator<SootClass> clsIt = Scene.v().getClasses().iterator();
		while (clsIt.hasNext()) {
			SootClass sClass = (SootClass) clsIt.next();
			if ( sClass.isPhantom() ) {
				// skip phantom classes
				continue;
			}
			if ( !sClass.isApplicationClass() ) {
				// skip library classes
				continue;
			}
			
			/* traverse all methods of the class */
			Iterator<SootMethod> meIt = sClass.getMethods().iterator();
			while (meIt.hasNext()) {
				SootMethod sMethod = (SootMethod) meIt.next();
				if ( !sMethod.isConcrete() ) {
					// skip abstract methods and phantom methods, and native methods as well
					continue; 
				}
				if ( sMethod.toString().indexOf(": java.lang.Class class$") != -1 ) {
					// don't handle reflections now either
					continue;
				}
				
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				CompleteUnitGraphEx cfg = new CompleteUnitGraphEx(sMethod.getActiveBody());
				Iterator<Unit> iter = cfg.iterator();
				while (iter.hasNext()) {
					Unit curu = iter.next();
					//System.out.println("\t" + curu + " has " + cfg.getSuccsOf(curu).size()+" descendants:");
					List<Unit> succs = unitToSuccs.get(curu);
					if (succs == null) {
						succs = new ArrayList<Unit>();
						unitToSuccs.put(curu, succs);
					}
					for (Unit u : cfg.getSuccsOf(curu)) {
						//System.out.println("\t\t"+ u + "");
						if (!succs.contains(u)) succs.add(u);
					}
					
					List<Unit> preds = unitToPreds.get(curu);
					if (preds == null) {
						preds = new ArrayList<Unit>();
						unitToPreds.put(curu, preds);
					}
					for (Unit u : cfg.getPredsOf(curu)) {
						//System.out.println("\t\t"+ u + "");
						if (!preds.contains(u)) preds.add(u);
					}
				}
				mToCfg.put(sMethod, cfg);
			}
		}
	} // - collectCFGs

	/** phase 2: add interprocedural (call/return) edges to connect all CFGs */
	private void connectInterproceduralEdges() {
		/* traverse all classes */
		Iterator<SootClass> clsIt = Scene.v().getClasses().iterator();
		while (clsIt.hasNext()) {
			SootClass sClass = (SootClass) clsIt.next();
			if ( sClass.isPhantom() ) {
				// skip phantom classes
				continue;
			}
			if ( !sClass.isApplicationClass() ) {
				// skip library classes
				continue;
			}
			
			/* traverse all methods of the class */
			Iterator<SootMethod> meIt = sClass.getMethods().iterator();
			while (meIt.hasNext()) {
				SootMethod sMethod = (SootMethod) meIt.next();
				if ( !sMethod.isConcrete() ) {
					// skip abstract methods and phantom methods, and native methods as well
					continue; 
				}
				if ( sMethod.toString().indexOf(": java.lang.Class class$") != -1 ) {
					// don't handle reflections now either
					continue;
				}
				
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				// call edge: connecting call site to entry of each possible callee
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);
				List<CallSite> cses = cfg.getCallSites();
				for (CallSite cs : cses) {
					List<SootMethod> appCallees = cs.getAppCallees();
					assert unitToSuccs.containsKey(cs.getLoc().getStmt()); // the call site must be in the caller's CFG
					List<Unit> succs = unitToSuccs.get(cs.getLoc().getStmt());
					for (SootMethod ce : appCallees) {
						//ReachableUsesDefs rudce = (ReachableUsesDefs) ProgramFlowGraph.inst().getCFG(ce);
						assert mToCfg.containsKey(ce);
						CompleteUnitGraphEx cecfg = mToCfg.get(ce);
						assert cecfg != null; // CFG for each method should have been created and cached
						
						if (!succs.contains(cecfg.ENTRY)) succs.add(cecfg.ENTRY);
						
						assert unitToPreds.containsKey(cecfg.ENTRY);
						List<Unit> preds = unitToPreds.get(cecfg.ENTRY);
						if (!preds.contains(cs.getLoc().getStmt()))	preds.add(cs.getLoc().getStmt());
					}
				}
				
				// return edges: connecting return site to each possible caller site
				assert mToCfg.containsKey(sMethod);
				CompleteUnitGraphEx cecfg = mToCfg.get(sMethod);
				assert unitToSuccs.containsKey(cecfg.EXIT);
				List<Unit> succs = unitToSuccs.get(cecfg.EXIT);
				
				List<CallSite> callerSites = cfg.getCallerSites();
				for (CallSite caller : callerSites) {
					// SootMethod mCaller = caller.getLoc().getMethod();
					// ReachableUsesDefs rudcaller = (ReachableUsesDefs)ProgramFlowGraph.inst().getCFG(mCaller);
					Stmt sCaller = caller.getLoc().getStmt();
					// As a shortcut, we just link the single EXIT node, instead of each return site, back to the caller site
					
					if (!succs.contains(sCaller)) succs.add(sCaller);
					succs.add(sCaller);
					
					assert unitToPreds.containsKey(sCaller);
					List<Unit> preds = unitToPreds.get(sCaller);
					if (!preds.contains(cecfg.EXIT)) preds.add(cecfg.EXIT);
				}
			}
		}
	} // - connectInterproceduralEdges
	
	/** phase 3: build the ICFG */
	public void buildGraph() {
		collectCFGs();
		connectInterproceduralEdges();
		buildHeadsAndTails();
		
		// clear accessory nodes (virtual ENTRY and EXIT nodes)
		/*
		for (SootMethod m : mToCfg.keySet()) {
			mToCfg.get(m).removeVirtualNodes();
		}
		*/
	} // buildGraph
	
	/** dump the graph structure of the Inter-procedural CFG */
	public void dumpGraph() {
		dumpGraph("=== the Interprocedural CFG ===");
	}
	
	public void dumpGraph(String header) {
		System.out.println();
		
		Queue<Unit> que = new LinkedList<Unit>();
		Set<Unit> visited = new LinkedHashSet<Unit>();
		
		System.out.println("\tHead nodes [size=" + getHeads().size()+"]:");
		for(Unit h: getHeads()) {
			System.out.println("\t\t"+ h);
			que.add(h);
		}
		
		while (!que.isEmpty()) {
			Unit n = que.poll();
			visited.add(n);

			assert n!=null;
			if (getSuccsOf(n) == null) continue;
			System.out.println("\t" + n + " has " + getSuccsOf(n).size()+" descendants:");
			for (Unit u : getSuccsOf(n)) {
				System.out.println("\t\t"+ u + "");
				if (!visited.contains(u) && !que.contains(u))
				{
					//visited.add(n);
					que.add(u);
				}
			}
		}

		System.out.println("\tTail nodes [size=" + getTails().size()+"]:");
		for(Unit t: getTails()) {
			System.out.println("\t\t"+ t);
		}
		//System.out.println("=========================================");
	}
	
	public boolean hasNode(Unit node) {
		return unitToSuccs.containsKey(node) && unitToPreds.containsKey(node);
	}
	
	// remove a node from the icfg and update edges the node is incident on accordingly
	public void removeNode(Unit node) {
		// 1. connect through
		for (Unit u : getPredsOf(node)) {
			// skip loop
			if (u == node) {
				continue;
			}
			for (Unit d : getSuccsOf(node)) {
				// skip loop and avoid loop too
				if (d == node || u == d) {
					continue;
				}
				if (getSuccsOf(u)!=null && !getSuccsOf(u).contains(d)) getSuccsOf(u).add(d);
				if (getPredsOf(d)!=null && !getPredsOf(d).contains(u)) getPredsOf(d).add(u);
			}
		}
		
		// 2. update upwards
		for (Unit u : getPredsOf(node)) {
			getSuccsOf(u).remove(node);
		}
			
		// 3. update downwards
		for (Unit d : getSuccsOf(node)) {
			getPredsOf(d).remove(node);
		}
		
		// 4. remove the node
		unitToPreds.remove(node);
		unitToSuccs.remove(node);
	}
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    private static final long serialVersionUID = 0x438200EE;
  
	/**
	 * Serialize the static VTG to a disk file whose name is given by sfn
	 * @param sfn the name of disk file into which the static VTG is to be dumped
	 * @return 0 for success and others for failure
	 */
	public int SerializeToFile(String sfn) {
		if ( !sfn.isEmpty() ) {
			FileOutputStream fos;
			try {
				fos = new FileOutputStream(sfn);
				ObjectOutputStream oos = new ObjectOutputStream(fos);
				oos.writeObject(this);
				//this.writeObject(oos);
				oos.flush();
				oos.close();
				return 0;
			}
			catch (Exception e) {
				e.printStackTrace();
				return -1;
			}
		}
		return -2;
	} // SerializeToFile
	
	public Object DeserializeFromFile(String dfn) {
		FileInputStream fis;
		try {
			fis = new FileInputStream(dfn);
			
			// reconstruct the static VTG from the given disk file 
			ObjectInputStream ois = new ObjectInputStream(fis);
			return ois.readObject();
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the source file from which the ICFG is deserialized specified as " + dfn);
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to InterCFGraphEx!");
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	} // DeserializeFromFile
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           VISUALIZATION OF ICFG (w.r.t DotGraph@Graphviz)
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	/** Serialize the ICFG into DotGraph format, which can be rendered by Graphviz Dot offline */
	public int visualizeGraph(String filename) {
		return visualizeGraph(filename, "Interprocedural Control Flow Graph");
	}
	
	public int visualizeGraph(String filename, String graphname) {
		if (filename.length() < 1) {
			// invalid name
			return -1;
		}
		
		final DotGraph canvas = new DotGraph(graphname);
		final DotGraphAttribute defaultNodeColor = new DotGraphAttribute("color", "black");
		final DotGraphAttribute defaultEdgeColor = new DotGraphAttribute("color", "black");
		
		// basic DotGraph settings
		canvas.setPageSize(8.5, 11.0);
		canvas.setNodeShape(DotGraphConstants.NODE_SHAPE_BOX);
		canvas.setNodeStyle(DotGraphConstants.NODE_STYLE_SOLID);
		canvas.setGraphLabel(graphname);
		canvas.setOrientation(DotGraphConstants.GRAPH_ORIENT_LANDSCAPE);
		
		// draw all nodes and edges
		for (Unit node : unitToSuccs.keySet()) {
			List<Unit> allSuccs = unitToSuccs.get(node);
			if (null == allSuccs) {
				// no successors, done
				continue;
			}
			for (Unit succ : allSuccs) {
				DotGraphNode dotNode = canvas.drawNode( node.toString() );
				dotNode.setAttribute(defaultNodeColor);
				dotNode.setLabel(node.toString());
				
				DotGraphEdge dotEdge = canvas.drawEdge(node.toString(), succ.toString());
				dotEdge.setAttribute(defaultEdgeColor);
				dotEdge.setLabel("");
				
				// Optional: discern edge types by color
				SootMethod m = ProgramFlowGraph.inst().getContainingMethod((Stmt)node);
				if (m==null) continue;
				assert mToCfg.containsKey(m);
				boolean isIntraEdge = mToCfg.get(m).getSuccsOf(node).contains(succ);
				if (isIntraEdge) {
					dotEdge.setAttribute("color", "red");
					dotEdge.setStyle(DotGraphConstants.EDGE_STYLE_SOLID);
				}
				else {
					dotEdge.setAttribute("color", "blue");
					dotEdge.setStyle(DotGraphConstants.EDGE_STYLE_DOTTED);
				}
			} // for each outgoing edge starting from the current Node
		} // for each graph Node
		
		canvas.plot(filename);
		return 0;
	}
}

/* vim :set ts=4 tw=4 tws=4 */
