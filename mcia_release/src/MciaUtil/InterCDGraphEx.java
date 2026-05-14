/**
 * File: src/McaiUtil/InterCDGraphEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/13/13		hcai		created; for computing, exceptional interprocedural control dependencies (CDs)
 *							for Diver upon the intraprocedural CDs computed by ControlDependeceEx
 * 09/01/13		hcai		added creating interprocedural exceptional CDs due to uncaught exceptions
 * 10/21/13		hcai		improved CDG BFS traversal (in dumpInterCDG and compuateInterproceduralCDs) that was 
 *							likely to gratingly drug due to repetitive node visits - first triggered when 
 *							running Diver on ArgoUML
 *  
*/
package MciaUtil;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.Stmt;
import soot.toolkits.graph.ExceptionalUnitGraph;

/**
 * A control dependency analyzer that computes interprocedural control dependencies covering
 * exceptional units (catch and finally blocks) for all classes and methods in a given subject
 * 
 *  Note: the interprocedural CDs can only be computed After the Intra-CD of All methods got ready 
 * @author hcai
 */
public abstract class InterCDGraphEx<NodeT, EdgeT extends VTEdge<NodeT>> {
	/** A map from method to its CDG, namely the graph that models its intra-CDs */
	protected Map<SootMethod, ControlDependenceEx<NodeT, EdgeT>> method2cdg;
		
	/** InterCDG edge set */
	protected Set<EdgeT> CDEdges;
	/** InterCDG node set */	
	protected Set<NodeT> CDNodes;
	/** map from a node to all outgoing edges */
	protected Map< NodeT, Set<EdgeT> > nodeToCDGEdges;
	/** map from a node to all incoming edges */
	protected Map< NodeT, Set<EdgeT> > nodeToInCDGEdges;
	/** the head(s) of the InterCDG */
	protected Set<NodeT> heads;
	/** the tail(s) of the InterCDG */
	protected Set<NodeT> tails;
	
	/** VTG-purpose edge set */
	protected Set<EdgeT> edges;
	/** VTG-purpose  node set */	
	protected Set<NodeT> nodes;
	/** map from a node to all outgoing edges */
	protected Map< NodeT, Set<EdgeT> > nodeToEdges;
	
	protected boolean debugOut;
	
	/** Symbolic mode: a coarse level of CD edge modeling, simply connecting from source stmt to the target stmt,
	 * with a symbolic variable as a place-holder in the VTG node's "variable" field, for a compatibility of CDG with VTG
	 * for a setting of false, defs at the source will be connected to uses at the target, namely an exhaustive set of detailed
	 * CDs will be created, to closely mesh into the value transfer model (same level of granularity) 
	 */
	protected boolean symbolicCD;
	
	/** if to form a holistic Interprocedural CDG (iCDG), as an option */
	protected boolean holisticInterCDG;
	
	/** if to create exceptional interprocedural CDs due to uncaught exceptions, connecting from callee back to callers */
	protected boolean exceptionalInterCD;
	/** given that we only care about declared exceptions and RunTime exceptions, choose if further ignore RunTime exceptions */
	protected boolean ignoreRuntimeExceptions;
		
	public InterCDGraphEx(boolean _debug) {
		method2cdg = new LinkedHashMap<SootMethod, ControlDependenceEx<NodeT, EdgeT>>();
		
		CDEdges = new LinkedHashSet<EdgeT>();
		CDNodes = new LinkedHashSet<NodeT>();
		nodeToCDGEdges = new LinkedHashMap<NodeT, Set<EdgeT>>();
		nodeToInCDGEdges = new LinkedHashMap<NodeT, Set<EdgeT>>();
		heads = new LinkedHashSet<NodeT>();
		tails = new LinkedHashSet<NodeT>();
		
		debugOut = _debug;
		symbolicCD = false;
		holisticInterCDG = false;
		
		exceptionalInterCD = false;
		ignoreRuntimeExceptions = false;
		
		edges = new LinkedHashSet<EdgeT>();
		nodes = new LinkedHashSet<NodeT>();
		nodeToEdges = new LinkedHashMap<NodeT, Set<EdgeT>>();
	}
	public InterCDGraphEx() {
		this(true);
	}
	public void turnDebug(boolean b) {
		debugOut = b;
	}
	public void turnSymbolicCD(boolean b) {
		symbolicCD = b;
	}
	public void turnHolisticCDG(boolean b) {
		holisticInterCDG = b;
	}
	public void turnExceptionalInterCD(boolean b) {
		exceptionalInterCD = b;
	}
	public void turnIgnoreRTECD(boolean b) {
		ignoreRuntimeExceptions = b;
	}
	public Set<NodeT> getHeads() {
		return heads;
	}
	public Set<NodeT> getTails() {
		return tails;
	}
	public void setMethodCDG(SootMethod m, ControlDependenceEx<NodeT, EdgeT> cdg) {
		method2cdg.put(m, cdg);
		if (holisticInterCDG) {
			// merge the CDG of this particular method to the whole iCDG graph structure
			for (EdgeT e : cdg.CDEdges) {
				addCDGEdge(e);
			}
		}
	}
	
	@Override public String toString() {
		return "Exceptional Inter-CDG [Static] " + CDNodes.size() + " nodes, " + CDEdges.size() + " edges ";
	}
	
	/** accessory routines similar to getSuccsOf/getPredsOf in terms of eventual functionalities,
	 * which is necessary for InterCDGraphEx to provide accesses to it as a modular CDG 
	 */
	public Set<EdgeT> getInCDGEdges(NodeT _node) {
		return nodeToInCDGEdges.get(_node); 
	}
	public Set<EdgeT> getOutCDGEdges(NodeT _node) {
		return nodeToCDGEdges.get(_node); 
	}
	abstract public Set<NodeT> getPredsOf(NodeT _node); //{ return null; }
	abstract public Set<NodeT> getSuccsOf(NodeT _node); //{ return null; }
	
	/** via invoking this interface before the CDG construction, control dependence graph can be merged into
	 * the value transfer graph for Diver  
	 * @param vtg the Diver static 
	 */
	public void joinTransferGraph(ValueTransferGraph<NodeT, EdgeT> vtg) {
		edges = vtg.edgeSet();
		nodes = vtg.nodeSet();
		nodeToEdges = vtg.nodeToEdges;
	}
	protected void buildHeadsAndTails() {
		for (NodeT n : CDNodes) {
			if (getOutCDGEdges(n)==null || getOutCDGEdges(n).size()<1) {
				tails.add(n);
			}
			if (getInCDGEdges(n)==null || getInCDGEdges(n).size()<1) {
				heads.add(n);
			}
		}
	}
		
	// descendants must create the edge according to the instantiated NodeT and EdgeT
	abstract protected Set<EdgeT> createSymbolicCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts);// {return null;}
	abstract protected Set<EdgeT> createFullCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts);// {return null;}
	abstract public void addEdge(EdgeT edge);// { edges.add(edge); }
	abstract public void addCDGEdge(EdgeT edge);// { CDEdges.add(edge); }
	abstract protected void createCDGEdge(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts);// {return null;}
	abstract public int dumpInternals(boolean listByMethod);
	abstract public int addInterCDs(NodeT src, NodeT tgt);
	abstract public int addMultiCSInterCDs(NodeT src);
	
	// compute interprocedural exceptional CDs due to uncaught exceptions
	abstract public int computeExceptionalInterCDs(SootMethod m, boolean ignoreRuntimeException);

	/** propagate intraprocedural CDs from the given method and beyond to create interprocedural CDs that all have sources in
	 * this given starting method
	 */
	public int compuateInterproceduralCDs(SootMethod m) {
		if (!method2cdg.containsKey(m) || null == method2cdg.get(m)) {
			System.err.println("Error: CDG for method " + m + " has not been computed yet!");
			return -1;
		}
		
		ControlDependenceEx<NodeT, EdgeT> mCDEx = method2cdg.get(m);
		Queue<NodeT> que = new PriorityQueue<NodeT>();
		Set<NodeT> visited = new LinkedHashSet<NodeT>();
		
		/* 
		// for debugging argoUML 
		if (m.getSignature().contains("InitPanelsLater: void run()")) {
			mCDEx.dumpCDG();
		}
		*/
		
		// we assume a complete CDG for mCDEx now
		assert mCDEx.getHeads().size()==1;
		que.add(mCDEx.getEntry());
		
		if (debugOut) { System.out.println(" compute ordinary inteprocedural CDs for method " + m.getSignature()); }
		while (!que.isEmpty()) {
			NodeT n = que.poll();
			visited.add(n);
			assert n!=null;
			
			// 1. interprocedural CDs through the single call site at the target			
			for (NodeT u : mCDEx.getSuccsOf(n)) {
				if (!visited.contains(u) && !que.contains(u)) {
					//visited.add(n);
					que.add(u);
				}
				if (u != n) {
					if (mCDEx.getHeads().contains(n)) {
						// it is too conservative to consider the ENTRY as a source of transitive interprocedural CD computation
						continue;
					}

					// transitive interprocedural CD computation starting from u
					addInterCDs(n, u);
				}
			} // for each intra-CD edge we are concerned about
			
			// 2. interprocedural CDs through multiple-target call site at the source
			addMultiCSInterCDs(n);

		} // BFS-traversal of the CDG
		
		// add Exceptional interprocedural CDs
		if (exceptionalInterCD) {
			if (debugOut) {System.out.println(" compute exceptional inteprocedural CDs for method " + m.getSignature());}
			int nret = computeExceptionalInterCDs(m, ignoreRuntimeExceptions);
			if (debugOut && nret != 0) {
				System.out.println("NOTE: " + nret + " exceptional inteprocedural CDs created from method " + m.getSignature());
			}
		}
		
		return 0;
	} // - compuateInterproceduralCDs
	
	/** compute all interprocedural CDs and fixate the interprocedural CDG finally */
	public void computeAllInterCDs() {
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
				
				if (sMethod.getActiveBody().getUnits().size() > 2000) {
					System.err.println(new Exception().getStackTrace()[0].getMethodName() + ": " + 
							sMethod.getSignature() + " skipped because of its oversize.");
					continue;
				}
				
				compuateInterproceduralCDs(sMethod);
				
			} // for each method
		} // for each class
		
		// fixate the interprocedural CDG as an independent (of VTG) graph
		if (holisticInterCDG) {
			this.buildHeadsAndTails();
			if (debugOut) {
				this.dumpInterCDG();
				this.dumpInternals(false);
			}
		}
		
	} // computeAllInterCDs
	
	/** dump the graph structure of the Inter-procedural CDG */
	public void dumpInterCDG() {
		System.out.println("=== the Interprocedural CDG ===");
		
		Queue<NodeT> que = new PriorityQueue<NodeT>();
		Set<NodeT> visited = new LinkedHashSet<NodeT>();
		
		System.out.println("\tHead nodes [size=" + getHeads().size()+"]:");
		for(NodeT h: getHeads()) {
			System.out.println("\t\t"+ h);
			que.add(h);
		}
		
		while (!que.isEmpty()) {
			NodeT n = que.poll();
			visited.add(n);

			assert n!=null;
			System.out.println("\t" + n + " has " + getSuccsOf(n).size()+" descendants:");
			for (NodeT u : getSuccsOf(n)) {
				System.out.println("\t\t"+ u + "");
				if (!visited.contains(u) && !que.contains(u))
				{
					//visited.add(n);
					que.add(u);
				}
			}
		}

		System.out.println("\tTail nodes [size=" + getTails().size()+"]:");
		for(NodeT t: getTails()) {
			System.out.println("\t\t"+ t);
		}
		//System.out.println("=========================================");
	}
}

/* vim :set ts=4 tw=4 tws=4 */
