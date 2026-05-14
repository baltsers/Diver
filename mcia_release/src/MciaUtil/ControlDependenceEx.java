/**
 * File: src/McaiUtil/ControlDependenceEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 07/30/13		hcai		created; for computing exceptional intra-procedural, control dependencies
 *							for Diver
 * 08/07/13		hcai		reached the first workable, complete exceptional intraprocedural CDs
 * 08/12/13		hcai		modeled complete CDG for a given CFG (method), ready for interprocedural CD computation
 * 10/21/13		hcai		fixed CDG BFS traversal (in dumpCDG) that was likely to get into drugging iterations due
 *							to repetitive node visits - first triggered when running Diver on ArgoUML
 * 10/22/13		hcai		added the cg instance member to hold the underlying CFG
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

import MciaUtil.CompleteUnitGraphEx.AugmentedUnit;

import dua.global.ProgramFlowGraph;
import dua.method.CFG.CFGNode;
import dua.util.Pair;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.IdentityStmt;
import soot.jimple.Stmt;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.DominatorNode;
import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.SimpleDominatorsFinder;
import soot.toolkits.graph.InverseGraph;
import soot.toolkits.graph.UnitGraph;
/** the following are not available in Soot 2.3.0 we are using now*/
/*
import soot.toolkits.graph.pdg.HashMutablePDG;
import soot.toolkits.graph.pdg.PDGNode;
import soot.toolkits.graph.pdg.PDGRegion;
import soot.toolkits.graph.pdg.Region;
*/

/**
 * A control dependency analyzer that computes intra-procedural control dependencies covering
 * exceptional units (catch and finally blocks) for a specific method (namely underlying CFG)
 * 
 * The CDG this models is therefore an intraprocedural one, calculated just based on the CFG of
 * the underlying method and intraprocedural post-dominance analysis.
 * 
 * @author hcai
 */
public abstract class ControlDependenceEx<NodeT, EdgeT extends VTEdge<NodeT>> {

	/** decide if a is ancestor of b in g, which must be a Tree! rather than a general graph */
	public static <N> boolean isAncestor(DirectedGraph<N> g, N a, N b) {
		if (a == null || g.getSuccsOf(a) == null || g.getSuccsOf(a).isEmpty()) { 
			return false;
		}
		if (g.getSuccsOf(a).contains(b)) {
			return true;
		}
		for (N n : g.getSuccsOf(a)) {
			//if (n==a) continue;
			if (isAncestor(g, n, b)) {
				return true;
			}
		}
		return false;
	}
	
	/** find the Least Common Ancestor of a and b in g, which must be a binary Tree! */
	public static <N> N LCA(DirectedGraph<N> g, N root, N a, N b) {
		if (root == null) {
			return null;
		}
		if (a == root || b == root) {
			return root;
		}
		assert g.getSuccsOf(root)==null || g.getSuccsOf(root).size()<=2;
		/*
		if (g.getSuccsOf(root).size()>=3) {
			System.out.println(root + " postdominates more than 2 nodes on the PDT:");
			for (N _n: g.getSuccsOf(root)) {
				System.out.println("\t"+_n);
			}
		}
		*/
		N lcal = null;
		if (null != g.getSuccsOf(root) && !g.getSuccsOf(root).isEmpty()) {
			lcal = LCA(g, g.getSuccsOf(root).get(0), a, b);
		}
		N lcar = null;
		if (null != g.getSuccsOf(root) && g.getSuccsOf(root).size()>=2) {
			lcar = LCA(g, g.getSuccsOf(root).get(1), a, b);
		}
		if (lcal != null && lcar != null) {
			return root;
		}
		if (lcal != null) { 
			return lcal;
		}
		
		return lcar;
	}
	
	/** find the Least Common Ancestor of a and b in g, which can be a general Tree! 
	 *	Warning: this version, produced by an attempt to adapt the LCA algorithm for binary tree, 
	 *	is not fully working for now; namely, there are bad cases for which it does not produce a right LCA 
	 */
	public static <N> N LCAEx(DirectedGraph<N> g, N root, N a, N b) {
		if (root == null) {
			return null;
		}
		
		if (g.getSuccsOf(root)==null || g.getSuccsOf(root).isEmpty()) {
			return null;
		}
		if (g.getSuccsOf(root).contains(a) && g.getSuccsOf(root).contains(b)) {
			return root;
		}
		if (g.getSuccsOf(a)!=null && g.getSuccsOf(a).contains(b)) {
			if (g.getPredsOf(a)!=null) {
				assert g.getPredsOf(a).size()==1;
				return g.getPredsOf(a).get(0);
			}
			// a is the root of the holistic tree
			assert g.getHeads().contains(a);
			return a;
		}
		if (g.getSuccsOf(b)!=null && g.getSuccsOf(b).contains(a)) {
			if (g.getPredsOf(b)!=null) {
				assert g.getPredsOf(b).size()==1;
				return g.getPredsOf(b).get(0);
			}
			// b is the root of the holistic tree
			assert g.getHeads().contains(b);
			return b;
		}
		
		N firstValid = null;
		boolean bAllValid = true;
		for (N child : g.getSuccsOf(root)) {
			N curlca = LCAEx(g, child, a, b);
			if (curlca==null) {
				bAllValid = false;
			}
			else if (firstValid==null){
				firstValid = curlca;
			}
		}
		if (bAllValid) {
			return root;
		}
		return firstValid;
	}
	
	/** find the Least Common Ancestor of a and b in g, which can be a general Tree! */
	// traverse backwardly from a given node to the root of the tree it is located
	public static <N> void getInverseFullPath(DirectedGraph<N> g, N n, List<N> path) {
		path.add(n);
		if (g.getHeads().contains(n) || null==g.getPredsOf(n) || g.getPredsOf(n).isEmpty()) {
			// the path contains the head itself already
			return;
		}
		// this algorithm only works for a Tree not a general graph
		assert g.getPredsOf(n).size()==1;
		getInverseFullPath(g, g.getPredsOf(n).get(0), path);
	}
	public static <N> N LCAOfGeneralTree(DirectedGraph<N> g, N a, N b) {
		List<N> ipatha = new ArrayList<N>();
		List<N> ipathb = new ArrayList<N>();
		getInverseFullPath(g, a, ipatha);
		getInverseFullPath(g, b, ipathb);
		Set<N> sa = new LinkedHashSet<N>(ipatha);
		Set<N> sb = new LinkedHashSet<N>(ipathb);
		// the common intersection
		boolean bret = sa.retainAll(sb);
		if (sa.isEmpty()) {
			// no common ancestor between a and b
			return null;
		}
		// the first intersection point should be the lowest common ancestor
		return sa.iterator().next();
	}
	
	/** find any Backward path from tgt to src in g, which can be a general graph! */
	public static <N> boolean getBackwardPath(DirectedGraph<N> g, N src, N tgt, List<N> path) {
		if (src==null || tgt==null) {
			return false;
		}
		if (g.getPredsOf(tgt)==null || g.getPredsOf(tgt).isEmpty()) {
			return false;
		}
		
		path.add(tgt);
		if (g.getPredsOf(tgt).contains(src)) {
			return true;
		}
		
		for (N n : g.getPredsOf(tgt)) {
			int cursize = path.size();
			if (!getBackwardPath(g, src, n, path)) {
				if (cursize >= 1) {
					// no path from the predecessor n
					List<N> toRemove = new ArrayList<N>();
					for (int i=cursize-1; i<path.size();++i) {
						toRemove.add(path.get(i));
					}
					path.removeAll(toRemove);
				}
			}
			else {
				// a path already found
				return true;
			}
		}
		
		// no any path exists
		return false;
	}
	
	@SuppressWarnings({ "unchecked", "unused" })
	private static <N> void listDominators(DominatorsFinder/*<N>*/ domFinder, boolean postdom) {
		Iterator<N> it = domFinder.getGraph().iterator();
		while (it.hasNext()) {
			N u = it.next();
			if (postdom) {
				System.out.println("Dominators of " + u + " are:");
			}
			else {
				System.out.println("Post-dominators of " + u + " are:");
			}
			if (null == domFinder.getDominators(u) || domFinder.getDominators(u).isEmpty()) {
				System.out.println("\t" + "EMPTY");
			}
			else {
				for (Object d : domFinder.getDominators(u)) {
					System.out.println("\t" + d);	
				}
			}
		}
	}
		
	/** CDG edge set */
	protected Set<EdgeT> CDEdges;
	/** CDG node set */	
	protected Set<NodeT> CDNodes;
	/** map from a node to all outgoing edges */
	protected Map< NodeT, Set<EdgeT> > nodeToCDGEdges;
	/** map from a node to all incoming edges */
	protected Map< NodeT, Set<EdgeT> > nodeToInCDGEdges;
	/** the head(s) of the CDG */
	protected List<NodeT> heads;
	/** the tail(s) of the CDG */
	protected List<NodeT> tails;
	/** the underlying method for this CDG */
	protected SootMethod sMethod;
	/** nodes depending on the ENTRY, namely the originally heads before adding the virtual ENTRY node */
	protected List<NodeT> entryDependents = null;
	
	/** VTG-purpose edge set */
	protected Set<EdgeT> edges;
	/** VTG-purpose  node set */	
	protected Set<NodeT> nodes;
	/** map from a node to all outgoing edges */
	protected Map< NodeT, Set<EdgeT> > nodeToEdges;
	
	private boolean debugOut;
	/** Symbolic mode: a coarse level of CD edge modeling, simply connecting from source stmt to the target stmt,
	 * with a symbolic variable as a place-holder in the VTG node's "variable" field, for a compatibility of CDG with VTG
	 * for a setting of false, defs at the source will be connected to uses at the target, namely an exhaustive set of detailed
	 * CDs will be created, to closely mesh into the value transfer model (same level of granularity) 
	 */
	private boolean symbolicCD;
	
	/** the underlying exceptional CFG */
	private CompleteUnitGraphEx cg  = null;
	public CompleteUnitGraphEx getCFG() { return cg; }
	
	public ControlDependenceEx(boolean _debug) {
		CDEdges = new LinkedHashSet<EdgeT>();
		CDNodes = new LinkedHashSet<NodeT>();
		nodeToCDGEdges = new LinkedHashMap<NodeT, Set<EdgeT>>();
		nodeToInCDGEdges = new LinkedHashMap<NodeT, Set<EdgeT>>();
		heads = new ArrayList<NodeT>();
		tails = new ArrayList<NodeT>();
		
		debugOut = _debug;
		symbolicCD = false;
		
		edges = new LinkedHashSet<EdgeT>();
		nodes = new LinkedHashSet<NodeT>();
		nodeToEdges = new LinkedHashMap<NodeT, Set<EdgeT>>();
	}
	public ControlDependenceEx() {
		this(true);
	}
	public void turnDebug(boolean b) {
		debugOut = b;
	}
	public void turnSymbolicCD(boolean b) {
		symbolicCD = b;
	}
	/** set Underlying CFG */
	public void setMethod(SootMethod m) {
		sMethod = m;
	}
	/** access the underlying method for which this CDG is modeled upon */
	public SootMethod getMethod() {
		return sMethod;
	}
	
	@Override public String toString() {
		return "Exceptional CDG [Static] for " + sMethod + ": " + CDNodes.size() + " nodes, " + CDEdges.size() + " edges ";
	}
	
	/** accessory routines similar to getSuccsOf/getPredsOf in terms of eventual functionalities,
	 * which is necessary for ControlDependenceEx to provide accesses to it as a modular CDG 
	 */
	public Set<EdgeT> getInCDGEdges(NodeT _node) { 
		return nodeToInCDGEdges.get(_node); 
	}
	public Set<EdgeT> getOutCDGEdges(NodeT _node) {
		return nodeToCDGEdges.get(_node); 
	}
	abstract public Set<NodeT> getPredsOf(NodeT _node); //{ return null; }
	abstract public Set<NodeT> getSuccsOf(NodeT _node); //{ return null; }

	public List<NodeT> getHeads() {
		return heads;
	}
	/** retrieve the single head node - ENTRY, after the virtual CD edges added */
	public NodeT getEntry() {
		if (heads==null || heads.isEmpty()) {
			// heads not built up yet
			return null;
		}
		return heads.get(0);
	}
	public List<NodeT> getTails() {
		return tails;
	}
	public List<NodeT> getEntryDependents() {
		return entryDependents;
	}
	
	/** via invoking this interface before the CDG construction, control dependence graph can be merged into
	 * the value transfer graph for Diver  
	 * @param vtg the Diver static 
	 */
	public void joinTransferGraph(ValueTransferGraph<NodeT, EdgeT> vtg) {
		edges = vtg.edgeSet();
		nodes = vtg.nodeSet();
		nodeToEdges = vtg.nodeToEdges;
	}
		
	// descendants must create the edge according to the instantiated NodeT and EdgeT
	abstract protected Set<EdgeT> createSymbolicCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts);// {return null;}
	abstract protected Set<EdgeT> createFullCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts);// {return null;}
	abstract public void addEdge(EdgeT edge);// { edges.add(edge); }
	abstract public void addCDGEdge(EdgeT edge);// { CDEdges.add(edge); }
	abstract protected void createCDGEdge(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts);// {return null;}
	abstract public int dumpInternals(boolean listByMethod);

	private DominatorNode searchPDTforNode(DominatorTreeAdapterEx dta, Unit tgt) {
		DominatorNode dn = null;
		Iterator<DominatorNode> iter = dta.iterator();
		while (iter.hasNext()) {
			dn = iter.next();
			if ((Unit)dn.getGode()==tgt) {
				break;
			}
		}
		return dn;
	}
	
	@SuppressWarnings("unchecked")
	public void dumpDTorPDT(DominatorTreeAdapterEx pdt, boolean bPDT) {
		Iterator<DominatorNode> iter = pdt.iterator();
		while (iter.hasNext()) {
			DominatorNode curn = iter.next();
			int sz = 0;
			if (pdt.getSuccsOf(curn)!=null) {
				sz = pdt.getSuccsOf(curn).size();
			}
			if (bPDT) {
				System.out.println("\t" + curn + " postdominates " + sz + " nodes on the PDT:");
			}
			else {
				System.out.println("\t" + curn + " dominates " + sz + " nodes on the DT:");
			}
			for (Object _n: pdt.getSuccsOf(curn)) {
				System.out.println("\t\t<"+ ((DominatorNode)_n).getGode() + ">");
			}
		}
	}
	abstract protected void buildHeadsAndTails(ExceptionalUnitGraph cg);
	/*
	{
		for (NodeT n : CDNodes) {
			if (getOutCDGEdges(n)==null || getOutCDGEdges(n).size()<1) {
				tails.add(n);
			}
			if (getInCDGEdges(n)==null || getInCDGEdges(n).size()<1) {
				heads.add(n);
			}
		}
	}
	*/

	/** add a Intra-CD edge from the virtual node ENTRY to each of the "raw heads", namely those having 
	 * no predecessors in current CDG
	 */
	abstract protected void addVirtualCDEdges();

	/** dump the graph structure of the Intra-procedural CDG for a CFG/method */
	public void dumpCDG() {
		System.out.println("=== the CDG of method " + sMethod + "===");
		if (getHeads().size()>1) {
			System.out.println("!!! The CDG of method " + sMethod + " has " + getHeads().size() + " heads!!");
		}
		
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
				if (!visited.contains(u) && !que.contains(u)) 
				{
					//visited.add(n);
					que.add(u);
				}
				System.out.println("\t\t"+ u + "");
			}
		}

		System.out.println("\tTail nodes [size=" + getTails().size()+"]:");
		for(NodeT t: getTails()) {
			System.out.println("\t\t"+ t);
		}
		//System.out.println("=========================================");
	}
	
	public int compuateIntraproceduralCDs(SootMethod sMethod, Set<EdgeT> localCDEdges) {
		this.setMethod(sMethod);
		return compuateIntraproceduralCDs(localCDEdges);
	}
	@SuppressWarnings("unchecked")
	public int compuateIntraproceduralCDs(Set<EdgeT> localCDEdges) {
		int nCDs = 0;
		Body body = sMethod.retrieveActiveBody();
		//ExceptionalUnitGraph ug = new ExceptionalUnitGraph(body);
		//CompleteUnitGraph cg = new CompleteUnitGraph(body);
		/** use the Exceptional Unit Graph as the underlying CFG for CDG construction, but ignoring implicit CD edges */
		//ExceptionalUnitGraph cg = new ExceptionalUnitGraph(body, PedanticThrowAnalysis.v(), true);
		//DirectedGraph<Unit> cg = new InverseGraph<Unit>(_cg);
		/*CompleteUnitGraphEx*/ cg = new CompleteUnitGraphEx(body);
		if (debugOut) {
			System.out.println("\nIntraprocedural CDs computation: now processing method " + sMethod + " .....");
			//cg.dumpCFG();
			//retrieveCDsFromPDG(cg);
		}
		
		/** construct intraprocedural control dependencies using Post-Domination analysis 
		 * with the assistance, when necessary, of domination analysis, both using Soot facilities 
		 */
		/*
		MHGDominatorsFinder domFinder = new MHGDominatorsFinder(ug);
		MHGPostDominatorsFinder pDomFinder = new MHGPostDominatorsFinder(ug);
		*/
		MHGDominatorsFinderEx domFinder = new MHGDominatorsFinderEx(cg);
		MHGPostDominatorsFinderEx pDomFinder = new MHGPostDominatorsFinderEx(cg);
		/*
		DominatorTree __DT = null;
		DominatorTree __PDT = null;
		*/
		DominatorTreeEx __DT = null;
		DominatorTreeEx __PDT = null;
		try {
			__DT = new DominatorTreeEx(domFinder);
			__PDT = new DominatorTreeEx(pDomFinder);
		}
		catch (Exception e) {
			/*
			SimpleDominatorsFinder sdom = new SimpleDominatorsFinder(ug);
			SimpleDominatorsFinder spdom = new SimpleDominatorsFinder(new InverseGraph<Unit>(ug));
			*/
			SimpleDominatorsFinder sdom = new SimpleDominatorsFinder(cg);
			SimpleDominatorsFinder spdom = new SimpleDominatorsFinder(new InverseGraph<Unit>(cg));
			__DT = new DominatorTreeEx(sdom);
			__PDT = new DominatorTreeEx(spdom);
		}
		catch (Throwable e) {
			e.printStackTrace();
		}

		DominatorTreeAdapterEx DT = new DominatorTreeAdapterEx(__DT);
		DominatorTreeAdapterEx PDT = new DominatorTreeAdapterEx(__PDT);
		
		if (debugOut) {
			/*
			System.out.println("=== The DT of method " + sMethod + " has " + PDT.size() + " nodes ===");
			dumpDTorPDT(DT, false);
			System.out.println("=== The PDT of method " + sMethod + " has " + PDT.size() + " nodes ===");
			dumpDTorPDT(PDT, true);
			*/
		}
		
		/** construct CDG based on the Augmented CFG (namely with start and exit nodes added) and the PDT,
		 * possibly with the assistance of DT for convenience purposes;
		 * use the Dragon Book algorithm for CDG construction
		 */
		Iterator<Unit> cgIter = cg.iterator();
		Set<Pair<Unit, Unit>> visitedEdges = new LinkedHashSet<Pair<Unit,Unit>>();
		while (cgIter.hasNext()) {
			Unit u = cgIter.next();
			DominatorNode dnu = searchPDTforNode(PDT,u);
			if (null == dnu) {
				System.out.println("ERROR !!! :" + u + " is not found in PDT");
				continue;
			}
			
			if (debugOut) {
				//listDominators(domFinder, false);
			}
			
			if (!(u instanceof AugmentedUnit)) {
				CFGNode nodeu = ProgramFlowGraph.inst().getNode((Stmt)u);
				if (nodeu.isSpecial() || nodeu.getStmt() instanceof IdentityStmt) {
					continue;
				}
			}
			
			if (null == cg.getSuccsOf(u)) {
				continue;
			}
			for (Unit v : cg.getSuccsOf(u)) {
				if (!(v instanceof AugmentedUnit)) {
					CFGNode nodev = ProgramFlowGraph.inst().getNode((Stmt)v);
					if (nodev.isSpecial() || nodev.getStmt() instanceof IdentityStmt) {
	 					continue;
					}
				}
				
				Pair<Unit,Unit> curEdge = new Pair<Unit,Unit>(u,v);
				if (visitedEdges.contains(curEdge)) {
					continue;
				}
				visitedEdges.add(curEdge);
				
				DominatorNode dnv = searchPDTforNode(PDT,v);
				
				if (isAncestor(PDT, dnv, dnu)) {
					continue;
				}
				
				assert PDT.getHeads().size()>=1;
				DominatorNode lca = null;
				lca = (DominatorNode)LCAOfGeneralTree(PDT, dnu, dnv);
				/*
				for (Object head : PDT.getHeads()) {
					//System.out.println("Try finding the LCA of " + u + " and " +v + " from head " + head);
					lca = (DominatorNode)LCAEx(PDT, (DominatorNode)head, dnu, dnv);
					if (lca != null) {
						List<DominatorNode> backPath = new ArrayList<DominatorNode>();
						if (getBackwardPath(PDT, lca, dnv, backPath)) {
							break;
						}
					}
				}
				//assert lca != null;
				*/
				if (lca == null) {
					System.out.println("[Warning]: cannot find the LCA of " + u + " and " +v);
					continue;
				}
				List<DominatorNode> backPath = new ArrayList<DominatorNode>();
				
				// there must be a backward path from v to lca
				boolean ret = getBackwardPath(PDT, lca, dnv, backPath);
				//assert ret==true;
				if (ret != true) {
					System.out.println("[Caution]: it is probably wrong that " + lca + " is found to be the LCA of " + u + " and " +v);
					continue;
				}
				if (lca == u) {
					backPath.add(lca);
				}
				
				// now, every node on the path should be control dependent on u
				for (DominatorNode _n : backPath) {
					Stmt srcs = (Stmt)u;
					Stmt tgts = (Stmt)_n.getGode();
					
					/** create VTG-purpose edges */
					Set<EdgeT> lcds;
					if (symbolicCD) {
						lcds = createSymbolicCDEdges(sMethod, srcs, sMethod, tgts);
					}
					else {
						lcds = createFullCDEdges(sMethod, srcs, sMethod, tgts);
					}
					if (localCDEdges != null) {
						localCDEdges.addAll(lcds);
					}
					nCDs += lcds.size();
					
					/** create CDG edge for constructing the CDG itself */
					createCDGEdge(sMethod, srcs, sMethod, tgts);
				}
			}
		} // for each qualified PDT edge
		
		// now that the CDs are computed, we need recover the original control flow graph by removing all virtual nodes and edges
		cg.removeVirtualNodes();
		
		// finalize the CDG as a complete graph
		this.buildHeadsAndTails(cg);
		this.addVirtualCDEdges();
		
		if (debugOut) {
			//this.dumpCDG();
			this.dumpInternals(false);
		}
		
		return nCDs;
	} // - getIntraproceduralCDs
	
	public void computeAllCDs() {
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
				
				Set<EdgeT> intraCDs = new LinkedHashSet<EdgeT>();
				int nCDs = compuateIntraproceduralCDs(sMethod, intraCDs);
				if (debugOut) {
					System.out.println(nCDs + " intraprocedural control dependencies computed for method " + 
							utils.getFullMethodName(sMethod));
					for (EdgeT e : intraCDs) {
						System.out.println(e);
					}
				}
			} // for each method
		} // for each class
	} // computeAllCDs
	
	/** the pdg package is not available in Soot 2.3.0 or lower releases */
	/*
	public static void dumpPDG(HashMutablePDG pdg) {
		System.out.println("\nProgram Dependence Graph for Method " + pdg.getCFG().getBody().getMethod());
		List<PDGNode> processed = new ArrayList<PDGNode>();
		Queue nodes = new LinkedList();
		nodes.offer(pdg.GetStartNode());
		
		while(nodes.peek() != null) {
			PDGNode node = (PDGNode) nodes.remove();
			processed.add(node);
			
			List succs = pdg.getSuccsOf(node);
			System.out.println("\t " + pdg.getDependents(node).size() + " nodes dependent on " + 
					node.getNode());
			
			int i = 0;
			Iterator itr = succs.iterator();
			while(itr.hasNext()) {
				PDGNode succ = (PDGNode)itr.next();
				List labels = pdg.getLabelsForEdges(node, succ);
				System.out.println("\t\t " + succ.getNode() + " with edge label " + labels);
				
				if(labels.get(0).equals("dependency")) {
					if(!processed.contains(succ)) {
						nodes.offer(succ);
					}
				}
			}
		}
	}
	*/
	
	/** the pdg package is not available in Soot 2.3.0 or lower releases */
	/*
	public void retrieveCDsFromPDG(UnitGraph ug, int format) {
		soot.toolkits.graph.pdg.HashMutablePDG pdg = new HashMutablePDG(ug);
		if (0 == format)	{
			pdg.printGraph();
			System.out.println(pdg);
			return;
		}
		
		if (1 == format) {
			Iterator<Unit> itug = ug.iterator(); 
			while (itug.hasNext()) {
				Unit curu = itug.next();
				PDGNode pn = pdg.getPDGNode(curu);
				if (null == pn) {
					System.out.println("\t No PDGNode for " + curu);
					continue;
				}
				System.out.println("\t " + pdg.getDependents(pn).size() + " nodes dependent on " + curu);
				for (PDGNode dpn : pdg.getDependents(pn)) {
					System.out.println("\t\t " + dpn.getNode());
				}
			}
			return;
		}
		
		dumpPDG(pdg);
	}
	*/
}

/* vim :set ts=4 tw=4 tws=4 */
