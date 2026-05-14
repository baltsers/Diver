/**
 * File: src/Diver/PIDynTransferGraph.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 07/05/13		hcai		created; defining the dynamic value transfer graph, as models 
 *							the dynamic value transfer relations from which dynamic impact sets are derived
 * 07/08/13		hcai		finished the initial graph construction, without pruning yet, based on the abstract base VTG
 * 07/22/13		hcai		reached the complete workable version of CD-less Diver after many bug fixes;
 * 07/23/13		hcai		added the pruning approach to impact set computation just for comparisons
 * 08/08/13		hcai		incorporated intraprocedural CDs
*/
package Diver;

import java.io.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import MciaUtil.*;
import MciaUtil.VTEdge.*;

/** A dynamic VTG node models the literal representation of a corresponding static VTG node
 */
final class PIDVTNode implements IVTNode<String, String, Integer> {
	/** variable underneath */
	protected final String v;
	/** enclosing/hosting method of the variable */
	protected final String m;
	/** statement location of the node */
	protected Integer s;
	
	/** a time stamp that relates the node to an execution trace */
	protected Integer timestamp;
	
	/** we may ignore stmt. loc. for some variables temporarily */
	public PIDVTNode(String _v, String _m) {
		v = _v;
		m = _m;
		s = null;
		timestamp = 0;
	}
	public PIDVTNode(String _v, String _m, Integer _s) {
		v = _v;
		m = _m;
		s = _s;
		timestamp = 0;
	}
	
	/** accessors */
	void setStmt(Integer _s) { this.s = _s; }
	public String getVar() { return v; }
	public String getMethod() { return m; }
	public Integer getStmt() { return s; }
	public void setTimestamp(Integer _ts) { timestamp = _ts; }
	public Integer getTimestamp() { return timestamp; }
	
	@Override public int hashCode() {
		/* NOTE: different types of variable can be assigned different hash code even though the underlying value is the same */
		//return (m.hashCode() & 0xffff0000) | (v.hashCode() & 0x0000ffff);
		//return (m.hashCode() & 0xffff0000) | (v.hashCode() & 0x0000ffff);
		return m.hashCode() + v.hashCode() + s.hashCode();
	}
	/** we do not distinguish two VTG nodes by statement location only */
	@Override public boolean equals(Object o) {
		boolean ret = v.equals(((PIDVTNode)o).v) && m.equals( ((PIDVTNode)o).m );
		if (ret && s != null) {
			return s.equals( ((PIDVTNode)o).s );
		}
		return ret;
	}
	/* exactly equal comparator */
	public boolean strictEquals(Object o) {
		return this.equals(o) && s.equals( ((PIDVTNode)o).s );
	}
	public String toStringNoStmt() {
		return "("+v+","+m+")";
	}
	@Override public String toString() {
		if (null != s) {
			return "("+v+","+m+","+s+")";
		}
		return "("+v+","+m+")";
	}

	public static class PIDVTNodeComparator implements Comparator<PIDVTNode> {
		private PIDVTNodeComparator() {}
		public static final PIDVTNodeComparator inst = new PIDVTNodeComparator();

		public int compare(PIDVTNode n1, PIDVTNode n2) {
			final String mname1 = n1.m;
			final String mname2 = n2.m;

			final String vname1 = n1.v;
			final String vname2 = n2.v;

			int cmpmName = mname1.compareToIgnoreCase(mname2);
			int cmpvName = vname1.compareToIgnoreCase(vname2);
			if (null == n1.s || null == n2.s) {
				return (cmpmName != 0)?cmpmName : cmpvName; 
			}

			final int sid1 = n1.s;
			final int sid2 = n2.s;
			return (cmpmName != 0)?cmpmName : (cmpvName != 0)?cmpvName:
				(sid1 > sid2)?1:(sid1 < sid2)?-1:0;
		}
	}
}

/** A dynamic VTG edge is the counterpart of corresponding VTG edge in the static VTG
 */
final class PIDVTEdge extends VTEdge<PIDVTNode> {
	public PIDVTEdge(PIDVTNode _src, PIDVTNode _tgt, VTEType _etype) {
		super(_src, _tgt, _etype);
	}
	/** exactly equal comparator */
	public boolean strictEquals(Object o) {
		return src.strictEquals(((PIDVTEdge)o).src) && tgt.strictEquals(((PIDVTEdge)o).tgt) 
			&& etype == ((PIDVTEdge)o).etype;
	}
	public String toString(boolean withStmt, boolean withType) {
		String ret = "<";
		ret += (withStmt)?src : src.toStringNoStmt();
		ret += ",";
		ret += (withStmt)?tgt : tgt.toStringNoStmt();
		ret += ">";
		if (withType) {
			ret += ":" + VTEdge.edgeTypeLiteral(etype);
		}
		return ret;
	}
	@Override public String toString() {
		return toString(true, true);
	}
}

/** the dynamic value transfer graph (dVTG) that models value flow relations between variables, 
 * both intra- and inter-procedurally that are inherited from the static VTG but exercised by some inputs
 *
 * dVTG serves tracing value flow of variables that actually propagates the impacts of original changes according
 * to a given set of operational profiles of the target subject program
 */
public class PIDynTransferGraph extends ValueTransferGraph<PIDVTNode, PIDVTEdge> implements Serializable {
	private static final long serialVersionUID = 0x638200DE;
	/* the static VTG as the source of the initial dynamic VTG */
	transient protected final static StaticTransferGraph svtg = new StaticTransferGraph();
	/* the full sequence of EAS events */
	transient protected static LinkedHashMap<Integer, String> EASeq = null;
	/* the file holding the execution trace being used */
	transient protected static String fnTrace = "";
	
	/* the file holding the static VTG binary */
	transient protected static String fnSVTG = "";
	
	// a map from a method to all transfer edges on the static graph that are associated with the method
	transient protected /*static*/ Map<String, List<PIDVTNode>> method2nodes;
	// a map from an edge type to all transfer edges of the type of the static graph
	transient protected /*static*/ Map<VTEdge.VTEType, List<PIDVTEdge>> type2edges;
	/** map from a node to all incoming edges */
	transient protected /*static*/ Map< PIDVTNode, Set<PIDVTEdge> > nodeToInEdges;
	
	/** a switch choosing whether to adopt the ReachingDefinition-style impact propagation, in which
	 *  a method A is regarded as impacted by method B only if there is some value defined by B reached some use of that value in A 
	 */
	static boolean reachingImpactPropagation = false; 

	public PIDynTransferGraph() {
		super();
	}
	
	protected void initInternals() {
		super.initInternals();
		//if (null==svtg) svtg = new StaticTransferGraph();
		/*if (null==method2nodes)*/ method2nodes = new LinkedHashMap<String, List<PIDVTNode>>();
		/*if (null==type2edges)*/ type2edges = new LinkedHashMap<VTEType, List<PIDVTEdge>>();
		/*if (null==nodeToInEdges)*/ nodeToInEdges = new LinkedHashMap< PIDVTNode, Set<PIDVTEdge> >();
	}
	
	public void setTrace(String _fnTrace) {
		fnTrace = _fnTrace;
	}
	public void setSVTG(String _fnSVTG) {
		fnSVTG = _fnSVTG;
	}
	public Set<PIDVTEdge> getInEdges(PIDVTNode _node) { 
		return nodeToInEdges.get(_node); 
	}
	
	@Override public String toString() {
		return "[Dynamic] " + super.toString(); 
	}
	
	public boolean isEmpty() {
		return super.isEmpty() || nodeToInEdges.isEmpty() || method2nodes.isEmpty() || type2edges.isEmpty();
	}
	public void clear() {
		super.clear();
		this.nodeToInEdges.clear();
		this.method2nodes.clear();
		this.type2edges.clear();
	}
	
	public void deepCopyFrom(PIDynTransferGraph vtg) {
		this.clear();
	
		for (PIDVTEdge _e : vtg.edges) {
			this.createTransferEdge(_e.getSource().getVar(), _e.getSource().getMethod(), _e.getSource().getStmt(),
					_e.getTarget().getVar(), _e.getTarget().getMethod(), _e.getTarget().getStmt(), _e.getEdgeType());
		}
		
		this.classifyEdgeAndNodes();
	}
	
	private void classifyEdgeAndNodes() {
		// 1. build the method->VTG nodes map to facilitate edge activation and source-target matching later on
		/* list nodes by enclosing methods */
		for (PIDVTNode vn : nodes) {
			List<PIDVTNode> vns = method2nodes.get(vn.getMethod());
			if (vns == null) {
				vns = new LinkedList<PIDVTNode>();
				method2nodes.put(vn.getMethod(), vns);
			}
			vns.add(vn);
		}
		// 2. build the EdgeType->VTG edges map 
		for (PIDVTEdge edge : edges) {
			List<PIDVTEdge> els = type2edges.get(edge.getEdgeType());
			if (els == null) {
				els = new LinkedList<PIDVTEdge>();
				type2edges.put(edge.getEdgeType(), els);
			}
			els.add(edge);
		}
	}
	
	public void CopyFrom(PIDynTransferGraph vtg) {
		this.clear();
		super.CopyFrom(vtg);
		
		nodeToInEdges = vtg.nodeToInEdges;
		method2nodes = vtg.method2nodes;
		type2edges = vtg.type2edges;
		//this.classifyEdgeAndNodes();
	}
	
	@Override public int buildGraph(boolean debugOut) throws Exception{
		for (SVTEdge se : svtg.edgeSet()) {
			createTransferEdge(
					utils.getCanonicalFieldName(se.getSource().getVar()),
					//utils.getFullMethodName(se.getSource().getMethod()),
					se.getSource().getMethod().getName(),
					utils.getFlexibleStmtId(se.getSource().getStmt()),
					utils.getCanonicalFieldName(se.getTarget().getVar()),
					//utils.getFullMethodName(se.getTarget().getMethod()),
					se.getTarget().getMethod().getName(),
					utils.getFlexibleStmtId(se.getTarget().getStmt()),
					se.getEdgeType());
		}
		return 0;
	}
	/**
	 * load the initializing static value transfer graph from a disk file previously dumped
	 * @param sfn the static graph file name
	 * @return 0 for success and others for failure
	 */
	public int initializeGraph(String sfn, boolean debugOut) {
		// 1. deserialize the static transfer graph firstly
		if ( null == svtg.DeserializeFromFile(sfn) ) {
			return -1;
		}
		
		// 2. initialize the dynamic graph with the literal representation of the underlying static graph
		try {
			buildGraph(false);
		}
		catch (Exception e) {
			return -1;
		}
		
		// 3. classify internal graph structures
		classifyEdgeAndNodes();
		
		if (debugOut) {
			System.out.println("original static graph: " + svtg);
			System.out.println("===== The Initial Dynamic VTG [loaded from the static counterpart] =====");
			dumpGraphInternals(true);
		}
	
		return 0;
	}
	public int initializeGraph(boolean debugOut) {
		if (null == fnSVTG || fnSVTG.length() < 1) {
			return -1;
		}
		return initializeGraph(fnSVTG, debugOut);
	}
		
	/**
	 * load execution trace to be used for exercising the static VTG into a dynamic one
	 * @param fnSource the source disk file holding an EA execution trace 
	 * @return 0 for success and others for failure, different values indicating different reasons
	 */
	protected int loadEASequence(String fnSource) {
		if (null == EASeq) {
			EASeq = new LinkedHashMap<Integer, String>();
		}
		else {
			EASeq.clear();
		}
		FileInputStream fis;
		try {
			fis = new FileInputStream(fnSource);
			
			ObjectInputStream ois = new ObjectInputStream(fis);
			@SuppressWarnings("unchecked")
			LinkedHashMap<Integer, String> readObject = (LinkedHashMap<Integer, String>) ois.readObject();
			EASeq = readObject;
			
			// --
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the given input EAS trace file " + fnSource);
			return -1;
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to LinkedHashMap<Integer, String>!");
			return -2;
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return 0;
	}
		
	protected void createTransferEdge(PIDVTNode src, PIDVTNode tgt, VTEType etype) {
		PIDVTEdge edge = new PIDVTEdge(src, tgt, etype);
		addEdge(edge);
	}

	/** a convenient routine for adding an edge and the covered nodes into the graph */
	private void createTransferEdge(String srcVar, String srcMethod, Integer srcStmt,
						String tgtVar, String tgtMethod, Integer tgtStmt, VTEType etype) {
		// TO DO:
		// any transfer edges associated with methods unreachable from entry should be ignored

		PIDVTNode src = new PIDVTNode(srcVar, srcMethod, srcStmt);
		PIDVTNode tgt = new PIDVTNode(tgtVar, tgtMethod, tgtStmt);
	
		createTransferEdge(src, tgt, etype);
	}
	
	public void addEdge(PIDVTEdge edge) {
		if (edges.contains(edge)) return;
		PIDVTNode src = edge.getSource(), tgt = edge.getTarget();
		
		nodes.add(src);
		nodes.add(tgt);
		edges.add(edge);
		
		Set<PIDVTEdge> outEdges = nodeToEdges.get(src);
		if (null == outEdges) {
			outEdges = new HashSet<PIDVTEdge>();
		}
		outEdges.add(edge);
		nodeToEdges.put(src, outEdges);
		
		Set<PIDVTEdge> inEdges = nodeToInEdges.get(tgt);
		if (null == inEdges) {
			inEdges = new HashSet<PIDVTEdge>();
		}
		inEdges.add(edge);
		nodeToInEdges.put(tgt, inEdges);
	}
	
	/**
	 * Create a dynamic transfer graph by first loading the static graph and then pruning edges according to the given
	 * execution trace;
	 * Without giving an origin of change, this intends to build a dynamic transfer graph for any later queries
	 */
	public int buildGraph(PIDynTransferGraph ndvtg, boolean debugOut) throws Exception{
		// 1. make sure the dynamic graph has been initialized successfully
		if (svtg.isEmpty() || this.isEmpty()) {
			// initializeGraph must be invoked and return success in the first place
			return -1;
		}
		// 2. load the trace
		if (null == fnTrace || fnTrace.length() < 1) {
			// trace not associated yet
			return -2;
		}
		if (0 != loadEASequence(fnTrace)) {
			// trace not loaded successfully
			return -3;
		}
		
		// - For DEBUG only
		if (debugOut) {
			System.out.println("===== The current execution trace under use [loaded from the call sequence] =====");
			TreeMap<Integer, String> treeA = new TreeMap<Integer, String> ( EASeq );
			System.out.println(treeA);
		}
		
		// 3. scan the execution trace and activate transfer edges
		// for different types of edges, we have different strategies for edge activation and source-target matching, so we maintain
		// a list of open source nodes for each edge type
		Map< VTEType, Set<PIDVTNode> > openNodes = new HashMap<VTEType, Set<PIDVTNode>>();
		for (VTEType etype : VTEType.values() /*type2edges.keySet()*/ ) {
			openNodes.put(etype, new LinkedHashSet<PIDVTNode>());
		}
		
		// the temporary dynamic VTG that keeps activated transfer edges only, will eventually substitute "this" dynamic graph
		PIDynTransferGraph dvtg = ndvtg; //new PIDynTransferGraph();
		String preMethod = null;
		
		for (Map.Entry<Integer, String> _event : EASeq.entrySet()) {
			String va = _event.getValue();
			if (va.equalsIgnoreCase("program start") || va.equalsIgnoreCase("program end")) {
				// these are just two special events marking start and termination of the run
				continue;
			}
			int endIdx = va.lastIndexOf(":");
			/* get the class and method name */
			assert endIdx >= 0;
			String em = _event.getValue().substring(0, endIdx);
			/* get the event type: enter or return */
			String etstr = va.substring(endIdx+1, va.length());
			boolean isEnterEvent = false;
			if (etstr.equalsIgnoreCase("e")) {
				// method enter event 
				isEnterEvent = true;
			}
			else if (etstr.equalsIgnoreCase("i")) {
				// method return event
				isEnterEvent = false;
			}
			else {
				// unexpectedly wrong event type flag
				assert false;
			}
						
			// check each of all nodes associated with the currently checked method
			if (method2nodes.get(em) == null) {
				//System.out.println("associated with no nodes: " + em);
				continue;
			}
			for (PIDVTNode _n : method2nodes.get(em)) {
				// attach the event's time stamp to the dynamic VTG node
				_n.setTimestamp(_event.getKey());
				
				if (isEnterEvent) {
					// examine each of all the outgoing edges from the node
					Set<PIDVTEdge> oedges = getOutEdges(_n);
					if (null != oedges) {
						for (PIDVTEdge _e : oedges) {
							// 1. local edges, all to be activated once the hosting method got executed
							if (_e.isLocalEdge()) {
								dvtg.addEdge(_e);
								continue;
							}

							// 3. for Intra CD edges, treat them the same way as Local edges
							if (_e.isIntraControlEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							
							// 2. for all other types of edge, we mark the source node as "open"
							openNodes.get(_e.getEdgeType()).add(_e.getSource());
							
							/*
							// 2. adjacent edges: activation depends on the adjacency of the source and target nodes' hosting methods
							if (_e.isAdjacentEdge()) {
								// 2.1 parameter edges: activation requires strict adjacency of hosting methods
								if (_e.isParameterEdge()) {
									if (!openNodes.get(VTEType.VTE_PARAM).contains(_e.getSource())) {
										// let the source be open now
										openNodes.get(VTEType.VTE_PARAM).add(_e.getSource());
									}
									continue;
								}
								
								// 2.2 return edges or RefParam edges : 
								assert _e.isRefReturnParamEdge() || _e.isReturnEdge();
							}
							*/
						} // for each outgoing edge
					}
					
					// examine each of all the incoming edges towards the node
					Set<PIDVTEdge> iedges = getInEdges(_n);
					if (iedges != null) {
						for (PIDVTEdge _e : iedges) {
							// 1. local edges, all to be activated once the hosting method got executed
							if (_e.isLocalEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							
							// 3. for Intra CD edges, treat them the same way as Local edges
							if (_e.isIntraControlEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							
							// 2. Heap object edges and parameter edges are activated upon the matching of the target with "open" source
							if (_e.isParameterEdge() || _e.isHeapEdge()) {
								// match open source for the target
								if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
									dvtg.addEdge(_e);
								}
								continue;
							}
							/*
							if (_e.isAdjacentEdge()) {
								// 2.1 parameter edges: activation requires strict adjacency of hosting methods
								if (_e.isParameterEdge()) {
									// the edge is to be activated only if its source has been "open" thus waiting for its target
									if (openNodes.get(VTEType.VTE_PARAM).contains(_e.getSource())) {
										dvtg.addEdge(_e);
									}
									continue;
								}
								
								// 2.2 return edges or RefParam edges : 
								assert _e.isRefReturnParamEdge() || _e.isReturnEdge();
							}
							*/
							// 4. for Inter CD edges, we treat them the way similar to Heap Edges
							if (_e.isInterControlEdge()) {
								// match open source for the target
								if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
									dvtg.addEdge(_e);
								}
							}

						} // for each incoming edge
					}
			
				} // if a method enter event
				else {
					/** upon ReturnedInto event, we need check the outgoing edges too, but 
					 * marking open nodes for Adjacent edges only
					 */
					// examine each of all the outgoing edges from the node
					Set<PIDVTEdge> oedges = getOutEdges(_n);
					if (null != oedges) {
						for (PIDVTEdge _e : oedges) {
							// 1. local edges, all to be activated once the hosting method got executed
							/** Local edges should have been activated when the enter event occurred, 
							 * which must happen before this returnInto event
							 */
							/*
							if (_e.isLocalEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							*/
							
							// 2. for return and RefParam edges, we mark the source node as "open"
							/** For outgoing heap object edges, we should have opened the source nodes upon the enter event of this method,
							 *  and, since those heap edges can transfer changes across any #methods away, they must not be "closed" once
							 *  opened in the occurrence of the enter event, which must happen before this returnInto event 
							 */
							if (_e.isAdjacentEdge()) {
								openNodes.get(_e.getEdgeType()).add(_e.getSource());
							}
						}
					}
					
					// examine each of all the incoming edges towards the node
					Set<PIDVTEdge> iedges = getInEdges(_n);
					if (null != iedges) {
						for (PIDVTEdge _e : iedges) {
							// 1. Local edges: have already been added when processing the enter event of the relevant methods
							
							// 2. Return edges follow the same rule of matching as the RefParam edges since the latter can be essntially
							//     regarded as a kind of Return
							if (_e.isReturnEdge() || _e.isRefReturnParamEdge() || _e.isHeapEdge()) {
								if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
									dvtg.addEdge(_e);
								}
								continue;
							}
						}
					}
				} // if a method ReturnedInto event
			} // for each associated node
			
			/** Return/RefParam/Param edges all follow the "matching by adjacency of the source and target method" rule; so we 
			 * 	 can close the "open" nodes for these types of edge that are associated with the predecessor event's method now
			 */
			if (null == preMethod || preMethod.equals(em)) {
				// nothing to do with the first event
				preMethod = em;
				continue;
			}
			
			// close some "open" source nodes
			for (Map.Entry< VTEType, Set<PIDVTNode> > _en : openNodes.entrySet()) {
				if ( ! (_en.getKey().equals(VTEType.VTE_PARAM) || _en.getKey().equals(VTEType.VTE_PARARET) ||
						_en.getKey().equals(VTEType.VTE_RET)) ) {
					// close nodes for "adjacent type" edges only
					continue;
				}
				Set<PIDVTNode> toRemove = new HashSet<PIDVTNode>();
				for (PIDVTNode _n : _en.getValue()) {
					// close nodes marked open by the previous event
					if (_n.getMethod().equals(preMethod)) {
						//openNodes.get(_en.getKey()).remove(_n);
						toRemove.add(_n);
					}
				}
				openNodes.get(_en.getKey()).removeAll(toRemove);
			}
			
			preMethod = em;
		} // for each method event in currently examined execution trace
		
		// now, update the graph to the really dynamic one
		/*
		this.CopyFrom(dvtg);
		this.classifyEdgeAndNodes();
		*/
		ndvtg.classifyEdgeAndNodes();
		
		return 0;
	}
	
	/**
	 * if user input gives method name only, or not matching any existing method name in upper/lower case,
	 * we first match "valid" names as an effective change set before computing the impact sets of them
	 * @param chg
	 * @return
	 */
	public Set<String> getChangeSet(String chg) {
		Set<String> chgSet = new LinkedHashSet<String>();
		for (String _m : method2nodes.keySet()) {
			if (_m.toLowerCase().contains(chg.toLowerCase())) {
				chgSet.add(_m);
			}
		}
		return chgSet;
	}
	
	private void getImpactSetImpl(PIDVTNode start, Set<PIDVTNode> visited, Set<String> mis) {
		if (!visited.add(start)) {
			return;
		}
		mis.add(start.getMethod());
		if (null == getOutEdges(start)) return;
		
		// find the incoming edge with maximal time stamp at its starting point
		int mts = Integer.MIN_VALUE;
		if (reachingImpactPropagation) {
			if (getInEdges(start) != null) {
				for (PIDVTEdge _in : getInEdges(start)) {
					mts = Math.max(mts, _in.getSource().getTimestamp());
				}
			}
		}
		for (PIDVTEdge _e : getOutEdges(start)) {
			if (reachingImpactPropagation) {
				if (_e.getSource().getTimestamp() < mts) {
					// stop propagation
					visited.add(_e.getTarget());
					continue;
				}
			}
			// continue propagation
			getImpactSetImpl(_e.getTarget(), visited, mis);
		}
	}
	
	public Set<String> getImpactSet(String chgm) {
		Set<String> mis = new LinkedHashSet<String>();
		// trivially the change method itself is always in the impact set of it
		//mis.add(chgm);
		
		Set<PIDVTNode> visited = new LinkedHashSet<PIDVTNode>();
		List<PIDVTNode> startNodes = method2nodes.get(chgm);
		if (startNodes != null) {
			for (PIDVTNode _n : startNodes) {
				getImpactSetImpl(_n, visited, mis);
			}
		}
				
		return mis;
	}
	
	/** a helper function, initialize the set of affected nodes by the given chgm, for 
	 * public Set<String> buildGraph(String chgm, boolean debugOut)
	 * namely, collect all directly reachable methods from chgm
	 */ 
	private void initAffectedNodes(Map<VTEType, Set<PIDVTNode>> nodes, VTEType etype, String chgm) {
		for (PIDVTNode _n : method2nodes.get(chgm)) {
			if (this.getOutEdges(_n) != null) {
				for (PIDVTEdge _e : this.getOutEdges(_n)) {
					//if (_e.getEdgeType().equals(etype)) 
					{
						nodes.get(etype).add(_e.getSource()); // any statement-level changes can happen at among these sources
						nodes.get(etype).add(_e.getTarget());
					}
				}
			}
		}
	}
	/** a helper function, updating affected nodes according to the current executed method, for 
	 * public Set<String> buildGraph(String chgm, boolean debugOut)
	 * namely, keep those that are directly reachable from any nodes in current set
	 */
	private void updateAffectedNodes(Map<VTEType, Set<PIDVTNode>> nodes, VTEType etype, String curm) {
		Set<PIDVTNode> nset = nodes.get(etype);
		if (nset == null || nset.isEmpty()) {
			// nothing to update
			return;
		}
		Set<PIDVTNode> _nset = new LinkedHashSet<PIDVTNode>(); // the new affected set
		for (PIDVTNode _n : nset) {
			if (this.getOutEdges(_n) != null) {
				for (PIDVTEdge _e : this.getOutEdges(_n)) {
					/** changes can be propagated forwards via any type of edges since we consider a single edge away here*/
					if (/*_e.getEdgeType().equals(etype) &&*/ _e.getTarget().getMethod().equals(curm)) {
						_nset.add(_e.getTarget());
					}
				}
			}
		}
		nset.clear();
		nset.addAll(_nset);
	}
	/**
	 * build a dynamic transfer graph for a specific change that has been given
	 * @param ndvtg the new dynamic transfer graph as the result of exercising the current dynamic graph with the current trace and chgm
	 * @param chgm the origin of change
	 * @return 0 for success otherwise failure
	 */
	public int buildGraph(PIDynTransferGraph ndvtg, String chgm, boolean debugOut) {
		// 1. make sure the dynamic graph has been initialized successfully
		if (svtg.isEmpty() || this.isEmpty()) {
			// initializeGraph must be invoked and return success in the first place
			return -1;
		}
		// 2. load the trace
		if (null == fnTrace || fnTrace.length() < 1) {
			// trace not associated yet
			return -2;
		}
		if (0 != loadEASequence(fnTrace)) {
			// trace not loaded successfully
			return -3;
		}
		
		// - For DEBUG only
		if (debugOut) {
			System.out.println("===== The current execution trace under use [loaded from the call sequence] =====");
			TreeMap<Integer, String> treeA = new TreeMap<Integer, String> ( EASeq );
			System.out.println(treeA);
		}
		
		// 3. scan the execution trace and activate transfer edges
		/** for different types of edges, we have different strategies for edge activation and source-target matching, so we maintain
		 * a list of open source nodes for each edge type
		 */
		Map< VTEType, Set<PIDVTNode> > openNodes = new HashMap<VTEType, Set<PIDVTNode>>();
		/** also, since we already know the query, we could record a propagation "flag" for each of the type of edge:
		 * more precisely, for Type 1 (Local) edges, the flag is always False, and for Type 3 (Heap object edges) it is always True;
		 * for Type 2 (one-method away, including parameterEdge, returnEdge and RefParamEdge) edges, the flag should be updated
		 * during the traversal according to the consecutive order in regard of the edge source method and edge target method
		 */
		Map<VTEType, Boolean> propFlags = new HashMap<VTEType, Boolean>();
		/** And, nodes to which the change from the origin (the query) has been propagated so far are recorded for deciding if we should
		 * mark nodes open, for each of the AdjacentEdges
		 */
		Map<VTEType, Set<PIDVTNode>> affectedNodes = new HashMap<VTEType, Set<PIDVTNode>>();
		for (VTEType etype : VTEType.values() /*type2edges.keySet()*/ ) {
			openNodes.put(etype, new LinkedHashSet<PIDVTNode>());
			/** Heap objects propagate changes across any number of intermediate methods if there is any edge connecting through*/
			propFlags.put(etype, !VTEdge.isAdjacentType(etype));
			affectedNodes.put(etype, new LinkedHashSet<PIDVTNode>());
		}
		/* 
		propFlags.put(VTEType.VTE_STVAR, true);
		propFlags.put(VTEType.VTE_INSVAR, true);
		propFlags.put(VTEType.VTE_ARRAYELE, true);
		*/
		
		// the temporary dynamic VTG that keeps activated transfer edges only, will eventually substitute "this" dynamic graph
		PIDynTransferGraph dvtg = ndvtg; //new PIDynTransferGraph();
		String preMethod = null;
		
		// mark the first enter event of the change method
		boolean bChgEnter = false;
		for (Map.Entry<Integer, String> _event : EASeq.entrySet()) {
			String va = _event.getValue();
			if (va.equalsIgnoreCase("program start") || va.equalsIgnoreCase("program end")) {
				// these are just two special events marking start and termination of the run
				continue;
			}
			int endIdx = va.lastIndexOf(":");
			/* get the class and method name */
			assert endIdx >= 0;
			String em = _event.getValue().substring(0, endIdx);
			
			if (!bChgEnter) {
				// em includes the class name and method name, together giving the origin of change
				bChgEnter = chgm.equalsIgnoreCase(em);
				if (!bChgEnter) {
					// methods occurred before the first enter of the change method won't be impacted by the change mehtod 
					continue;
				}
			}
			
			/* get the event type: enter or return */
			String etstr = va.substring(endIdx+1, va.length());
			boolean isEnterEvent = false;
			if (etstr.equalsIgnoreCase("e")) {
				// method enter event 
				isEnterEvent = true;
			}
			else if (etstr.equalsIgnoreCase("i")) {
				// method return event
				isEnterEvent = false;
			}
			else {
				// unexpectedly wrong event type flag
				assert false;
			}
						
			// check each of all nodes associated with the currently checked method
			if (method2nodes.get(em) == null) {
				//System.out.println("associated with no nodes: " + em);
				continue;
			}
			
			// update the "propagation flags" per currently encountered method
			for (VTEType etype : VTEType.values()/*type2edges.keySet()*/ ) {
				if (VTEdge.isAdjacentType(etype)) {
					// start or stop propagating change impact via Adjacent edges, depending on it the chgm occurred					
					propFlags.put(etype, /*isEnterEvent &&*/ em.equalsIgnoreCase(chgm));
				}
			}
			
			//if (isEnterEvent) {
				if (propFlags.get(VTEType.VTE_PARAM)) {
					initAffectedNodes(affectedNodes, VTEType.VTE_PARAM, chgm);
				}
				else {
					updateAffectedNodes(affectedNodes, VTEType.VTE_PARAM, em);
				}
				
				if (propFlags.get(VTEType.VTE_RET)) {
					initAffectedNodes(affectedNodes, VTEType.VTE_RET, chgm);
				}
				else {
					updateAffectedNodes(affectedNodes, VTEType.VTE_RET, em);
				}
				
				if (propFlags.get(VTEType.VTE_PARARET)) {
					initAffectedNodes(affectedNodes, VTEType.VTE_PARARET, chgm);
				}
				else {
					updateAffectedNodes(affectedNodes, VTEType.VTE_PARARET, em);
				}/*
			}
			else {
				updateAffectedNodes(affectedNodes, VTEType.VTE_RET, em);
				updateAffectedNodes(affectedNodes, VTEType.VTE_PARARET, em);
			}*/
			
			for (PIDVTNode _n : method2nodes.get(em)) {
				// attach the event's time stamp to the dynamic VTG node
				_n.setTimestamp(_event.getKey());
				
				if (isEnterEvent) {
					// examine each of all the outgoing edges from the node
					Set<PIDVTEdge> oedges = getOutEdges(_n);
					if (null != oedges) {
						for (PIDVTEdge _e : oedges) {
							// 1. local edges, all to be activated once the hosting method got executed
							if (_e.isLocalEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							/*
							if (ValueTransferGraph.isAdjacentType(_e.getEdgeType())) {
								if (propFlags.get(_e.getEdgeType())) {
									initAffectedNodes(affectedNodes, _e.getEdgeType(), chgm);
								}
								else {
									updateAffectedNodes(affectedNodes, _e.getEdgeType(), em);
								}
							}
							*/
							
							// 3. for Intra CD edges, treat them the same way as Local edges
							if (_e.isIntraControlEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							
							// 2. for Heap edges, we mark the source node as "open"; for AdjacentEdges, it depends on its 
							// being in the affectedNodes or not
							if (!VTEdge.isAdjacentType(_e.getEdgeType()) || 
									affectedNodes.get(_e.getEdgeType()).contains(_e.getSource()) ) {
								openNodes.get(_e.getEdgeType()).add(_e.getSource());
								continue;
							}
							
							// 4. for Inter CD edges, we treat them the way similar to Adjacent Edges but would not worry about multi-hop
							// propagation, so we always add open the source nodes
							/** this has been covered by !ValueTransferGraph.isAdjacentType() in for case 2 above however */
							/*
							if (_e.isInterControlEdge()) {
								openNodes.get(_e.getEdgeType()).add(_e.getSource());
							}
							*/
						} // for each outgoing edge
					}
					
					// examine each of all the incoming edges towards the node
					Set<PIDVTEdge> iedges = getInEdges(_n);
					if (iedges != null) {
						for (PIDVTEdge _e : iedges) {
							// 1. local edges, all to be activated once the hosting method got executed
							if (_e.isLocalEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							
							// 2. Heap object edges and parameter edges are activated upon the matching of the target with "open" source
							if (_e.isParameterEdge() || _e.isHeapEdge()) {
								// match open source for the target
								if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
									dvtg.addEdge(_e);
								}
								continue;
							}
							
							// 3. for Intra CD edges, treat them the same way as Local edges
							if (_e.isIntraControlEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							
							// 4. for Inter CD edges, we treat them the way similar to Heap Edges
							if (_e.isInterControlEdge()) {
								// match open source for the target
								if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
									dvtg.addEdge(_e);
								}
							}
						} // for each incoming edge
					}
				} // if a method enter event
				else {
					/** upon ReturnedInto event, we need check the outgoing edges too, but 
					 * marking open nodes for adjacent edges only
					 */
					// examine each of all the outgoing edges from the node
					Set<PIDVTEdge> oedges = getOutEdges(_n);
					if (null != oedges) {
						for (PIDVTEdge _e : oedges) {
							// 1. local edges, all to be activated once the hosting method got executed
							/** Local edges should have been activated when the enter event occurred, 
							 * which must happen before this returnInto event
							 */
							/*
							if (_e.isLocalEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							*/
							
							// 2. for Adjacent edges, we mark the source node as "open"
							/** For outgoing heap object edges, we should have opened the source nodes upon the enter event of this method,
							 *  and, since those heap edges can transfer changes across any #methods away, they must not be "closed" once
							 *  opened in the occurrence of the enter event, which must happen before this returnInto event 
							 */
							if ( _e.isAdjacentEdge() && affectedNodes.get(_e.getEdgeType()).contains(_e.getSource()) ){
								openNodes.get(_e.getEdgeType()).add(_e.getSource());
								continue;
							}
							
							// 3. intra CD edges, like other Local edges, should have been activated in the advent of enter event
							/*
							if (_e.isIntraControlEdge()) {
								dvtg.addEdge(_e);
								continue;
							}
							*/
							
							// 4. for Inter CD edges, we treat them the way similar to Adjacent Edges but would not worry about multi-hop
							// propagation, so we always add open the source nodes
							/** but, like Heap object edges, we should have opened the source nodes upon the enter event of this method, and 
							 * since they must not be closed once opened, we do not need to open them again as a waste of operations
							 */
							/*
							if (_e.isInterControlEdge()) {
								openNodes.get(_e.getEdgeType()).add(_e.getSource());
							}
							*/
						}
					}
					
					// examine each of all the incoming edges towards the node
					Set<PIDVTEdge> iedges = getInEdges(_n);
					if (null != iedges) {
						for (PIDVTEdge _e : iedges) {
							// 1. Local edges: have already been added when processing the enter event of the relevant methods
							
							// 2. Return edges follow the same rule of matching as the RefParam edges since the latter can be essentially
							//     regarded as a kind of Return;
							// And, heap object edges can also transfer changes from callee to caller
							if (_e.isReturnEdge() || _e.isRefReturnParamEdge() || _e.isHeapEdge()) {
								if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
									dvtg.addEdge(_e);
								}
								continue;
							}
							
							// 3. Intra CD edges: have already been added when processing the enter event of the relevant methods
							
							// 4. Inter CD edges are added when the target gets paired ONLY upon the entrance of the target method
							// just like the Parameter edges
						}
					}
				} // if a method ReturnedInto event
			} // for each associated node
			
			/** Return/RefParam/Param edges all follow the "matching by adjacency of the source and target method" rule; so we 
			 * 	 can close the "open" nodes for these types of edge that are associated with the predecessor event's method now
			 */
			if (null == preMethod || preMethod.equals(em)) {
				// nothing to do with the first event
				preMethod = em;
				continue;
			}
			// close some "open" source nodes
			for (Map.Entry< VTEType, Set<PIDVTNode> > _en : openNodes.entrySet()) {
				//if ( ! (_en.getKey().equals(VTEType.VTE_PARAM) || _en.getKey().equals(VTEType.VTE_PARARET) ||	_en.getKey().equals(VTEType.VTE_RET)) ) {
				/** Interprocedural CD edges can pass across any number of methods, like Heap object transfer edges */
				if ( !VTEdge.isAdjacentType(_en.getKey()) /*&& !ValueTransferGraph.isControlType(_en.getKey()) */) {
					// close nodes for "adjacent type" edges only
					continue;
				}
				Set<PIDVTNode> toRemove = new HashSet<PIDVTNode>();
				for (PIDVTNode _n : _en.getValue()) {
					// close nodes marked open by the previous event
					if (_n.getMethod().equals(preMethod)) {
						//openNodes.get(_en.getKey()).remove(_n);
						toRemove.add(_n);
					}
				}
				openNodes.get(_en.getKey()).removeAll(toRemove);
			}
			
			preMethod = em;
			
		} // for each method event in currently examined execution trace
		
		// now, update the graph to the really dynamic one
		/*
		this.CopyFrom(dvtg);
		this.classifyEdgeAndNodes();
		*/
		ndvtg.classifyEdgeAndNodes();
		
		return 0;
	}
	
	/**
	 * As an alternative to the "source-target matching" approaches above, the pruning approach can be even more conservative;
	 * implemented for a comparison with it; The pruned graph is intended to be applicable for any later queries relative to the 
	 * current execution trace
	 * @param ndvtg 
	 * @param debugOut logging the computation process for debugging purposes
	 * @return 0 for success and others for failures
	 */
	public int pruneGraph(PIDynTransferGraph ndvtg, boolean debugOut) {
		// 1. make sure the dynamic graph has been initialized successfully
		if (svtg.isEmpty() || this.isEmpty()) {
			// initializeGraph must be invoked and return success in the first place
			return -1;
		}
		// 2. load the trace
		if (null == fnTrace || fnTrace.length() < 1) {
			// trace not associated yet
			return -2;
		}
		if (0 != loadEASequence(fnTrace)) {
			// trace not loaded successfully
			return -3;
		}
		
		// - For DEBUG only
		if (debugOut) {
			System.out.println("===== The current execution trace under use [loaded from the call sequence] =====");
			TreeMap<Integer, String> treeA = new TreeMap<Integer, String> ( EASeq );
			System.out.println(treeA);
		}
		
		/*
		// before pruning, make a clone of the initial dvtg, which will be reused by later execution traces
		ndvtg.deepCopyFrom(this);
		*/
		
		// index methods appeared in the current execution trace
		List<String> methodInSeq = new ArrayList<String>();
		List<Boolean> eventTypeInSeq = new ArrayList<Boolean>();
		for (Map.Entry<Integer, String> _event : EASeq.entrySet()) {
			String va = _event.getValue();
			if (va.equalsIgnoreCase("program start") || va.equalsIgnoreCase("program end")) {
				// these are just two special events marking start and termination of the run
				continue;
			}
			int endIdx = va.lastIndexOf(":");
			/* get the class and method name */
			assert endIdx >= 0;
			String em = _event.getValue().substring(0, endIdx);
			
			/* get the event type: enter or return */
			String etstr = va.substring(endIdx+1, va.length());
			boolean isEnterEvent = false;
			if (etstr.equalsIgnoreCase("e")) {
				// method enter event 
				isEnterEvent = true;
			}
			else if (etstr.equalsIgnoreCase("i")) {
				// method return event
				isEnterEvent = false;
			}
			else {
				// unexpectedly wrong event type flag
				assert false;
			}
			
			methodInSeq.add(em);
			eventTypeInSeq.add(isEnterEvent);
		}
		
		Set<PIDVTEdge> toPrune = new LinkedHashSet<PIDVTEdge>();
		
		// 3. prune edges containing nodes whose associated method is never executed
		for (PIDVTEdge _e : edges) {
			if ( !methodInSeq.contains(_e.getSource().getMethod()) || !methodInSeq.contains(_e.getTarget().getMethod()) ) {
				toPrune.add(_e);
			}
		}
		
		// 4. prune parameter edges whose source is never immediately followed by the target in the trace
		for (PIDVTEdge _e : edges) {
			if ( !_e.isParameterEdge() ) {
				// prune parameter edges here only
				continue;
			}
			boolean bPaired = false;
			for (int i = 0; i < methodInSeq.size()-1; ++i) {
				if ( methodInSeq.get(i).equals(_e.getSource().getMethod()) &&   
						methodInSeq.get(i+1).equals(_e.getTarget().getMethod()) &&
						eventTypeInSeq.get(i+1)==true ) {
					// paired only when the target follows the source at its heed and the target occurs as a "method Enter" event
					bPaired = true;
					break;
				}
			}
			if (!bPaired) {
				toPrune.add(_e);
			}
		}
		
		// 5. prune return edges whose source (the callee) is never immediately followed by the target (the caller) in the trace
		for (PIDVTEdge _e : edges) {
			if ( !(_e.isRefReturnParamEdge() || _e.isReturnEdge()) ) {
				// prune Return and RefParam edges here only
				continue;
			}
			boolean bPaired = false;
			for (int i = 0; i < methodInSeq.size()-1; ++i) {
				if ( methodInSeq.get(i).equals(_e.getSource().getMethod()) &&   
						methodInSeq.get(i+1).equals(_e.getTarget().getMethod()) &&
						eventTypeInSeq.get(i+1)==false ) {
					// paired only when the target follows the source at its heed and the target occurs as a "method ReturnedInto" event
					bPaired = true;
					break;
				}
			}
			if (!bPaired) {
				toPrune.add(_e);
			}
		}
		
		// 6. prune Heap edges whose source (the writer) never appeared prior to the target (the reader) in the trace
		/** Inter-procedural CD edges are pruned in the same way as Heap object edges */
		for (PIDVTEdge _e : edges) {
			if ( !_e.isHeapEdge() && !_e.isInterControlEdge()) {
				// prune Heap Object edges and Interprocedural CD edges here only
				continue;
			}
			
			// the first occurrence of the source
			int iSource = methodInSeq.indexOf(_e.getSource().getMethod());
			// the last occurrence of the target
			int iTarget = methodInSeq.lastIndexOf(_e.getTarget().getMethod());
			
			if (!(iSource < iTarget)) {
				toPrune.add(_e);
			}
		}
		
		// 7. for Local edges and Intraprocedural CD edges, they should have been pruned when pruning all edges connecting
		// methods that never appear in the trace
		
		if (debugOut) {
			System.out.println(toPrune.size() + " edges to be pruned per current execution trace.");
		}
		
		// form the exercised dynamic VTG by discarding all edges in the "to Prune" set
		for (PIDVTEdge _e : edges) {
			if (!toPrune.contains(_e)) {
				ndvtg.addEdge(_e);
			}
		}
		
		ndvtg.classifyEdgeAndNodes();
		
		return 0;
	}
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	@Override public PIDynTransferGraph DeserializeFromFile(String sfn) {
		Object o = super.DeserializeFromFile(sfn);
		if (o != null) {
			PIDynTransferGraph vtg = new PIDynTransferGraph();
			vtg = (PIDynTransferGraph)o;
			//vtg.readObject(ois);
			this.CopyFrom(vtg);
			return vtg;
		}
			
		return null;
	} // DeserializeFromFile
	
	/**
	 * for debugging purposes, list all edge details
	 * @param listByEdgeType
	 */
	@Override public int dumpGraphInternals(boolean listByEdgeType) {
		if (0 == super.dumpGraphInternals(listByEdgeType)) {
			return 0;
		}
		
		for (Map.Entry<String, List<PIDVTNode>> en : method2nodes.entrySet()) {
			System.out.println("----------------------------------------- " + 
					en.getKey() + " [" +	en.getValue().size() + 
					" nodes] -----------------------------------------");
			for (PIDVTNode vn : en.getValue()) {
				System.out.println("\t"+vn);
			}
		}
		
		/* list edges by types */
		for (Map.Entry<VTEType, List<PIDVTEdge>> en : type2edges.entrySet()) {
			System.out.println("----------------------------------------- " + 
					VTEdge.edgeTypeLiteral(en.getKey()) + " [" +	en.getValue().size() + 
					" edges] -----------------------------------------");
			for (PIDVTEdge edge : en.getValue()) {
				System.out.println("\t"+edge);
			}
		}
		return 0;
	}
} // definition of PIDynTransferGraph

/* vim :set ts=4 tw=4 tws=4 */
