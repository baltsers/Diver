/**
 * File: src/Diver/DynTransferGraph.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 07/05/13		hcai		created; defining the dynamic value transfer graph, as models 
 *							the dynamic value transfer relations from which dynamic impact sets are derived
 * 07/08/13		hcai		finished the initial graph construction, without pruning yet, based on the abstract base VTG
 * 07/22/13		hcai		reached the complete workable version of CD-less Diver after many bug fixes;
 * 07/23/13		hcai		added the pruning approach to impact set computation just for comparisons
 * 08/08/13		hcai		incorporated intraprocedural CDs
 * 09/04/13		hcai		speed up Diver impact set computation by storing method indices instead of method signature
 *							in the Dynamic VTG nodes; and by reading multi-segment trace per test if applicable
 * 10/18/13		hcai		adapted all query algorithms to multi-segment trace per test if applicable		
 * 10/25/13		hcai		applied runtime coverage pruning
 * 11/04/13		hcai		added options for either pre-pruning or post-pruning the MDG nodes and edges according to
 *							coverage information
 * 11/08/13		hcai		applied dynamic alias monitoring data to impact computation
 * 11/15/13		hcai		fixed the edge pruning algorithm based on dynamic alias monitoring data
 *
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
import java.util.zip.GZIPInputStream;

import MciaUtil.*;
import MciaUtil.VTEdge.*;

/** A dynamic VTG node models the literal representation of a corresponding static VTG node
 */
final class DVTNode implements IVTNode<String, Integer, Integer> {
	/** variable underneath */
	protected final String v;
	/** enclosing/hosting method of the variable */
	protected final Integer m;
	/** statement location of the node */
	protected Integer s;
	
	/** a time stamp that relates the node to an execution trace */
	protected Integer timestamp;
	
	/** we may ignore stmt. loc. for some variables temporarily */
	public DVTNode(String _v, Integer _m) {
		v = _v;
		m = _m;
		s = null;
		timestamp = 0;
	}
	public DVTNode(String _v, Integer _m, Integer _s) {
		v = _v;
		m = _m;
		s = _s;
		timestamp = 0;
	}
	
	/** accessors */
	void setStmt(Integer _s) { this.s = _s; }
	public String getVar() { return v; }
	public Integer getMethod() { return m; }
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
		boolean ret = v.equals(((DVTNode)o).v) && m.equals( ((DVTNode)o).m );
		if (ret && s != null) {
			return s.equals( ((DVTNode)o).s );
		}
		return ret;
	}
	/* exactly equal comparator */
	public boolean strictEquals(Object o) {
		return this.equals(o) && s.equals( ((DVTNode)o).s );
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

	public static class DVTNodeComparator implements Comparator<DVTNode> {
		private DVTNodeComparator() {}
		public static final DVTNodeComparator inst = new DVTNodeComparator();

		public int compare(DVTNode n1, DVTNode n2) {
			final Integer mname1 = n1.m;
			final Integer mname2 = n2.m;

			final String vname1 = n1.v;
			final String vname2 = n2.v;

			int cmpmName = mname1 - mname2;
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
final class DVTEdge extends VTEdge<DVTNode> {
	public DVTEdge(DVTNode _src, DVTNode _tgt, VTEType _etype) {
		super(_src, _tgt, _etype);
	}
	/** exactly equal comparator */
	public boolean strictEquals(Object o) {
		return src.strictEquals(((DVTEdge)o).src) && tgt.strictEquals(((DVTEdge)o).tgt) 
			&& etype == ((DVTEdge)o).etype;
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
public class DynTransferGraph extends ValueTransferGraph<DVTNode, DVTEdge> implements Serializable {
	private static final long serialVersionUID = 0x638200DE;
	/* the static VTG as the source of the initial dynamic VTG */
	transient protected final static StaticTransferGraph svtg = new StaticTransferGraph();
	/* the full sequence of EAS events */
	transient protected static LinkedHashMap<Integer, Integer> EASeq = null;
	/* the map from index to method signature associated with the full sequence of method events */
	transient protected static LinkedHashMap<Integer, String> EAMethodMap = null;
	
	/* the file holding the execution trace being used */
	transient protected static String fnTrace = "";
	
	/* the file holding the static VTG binary */
	transient protected static String fnSVTG = "";
	
	// a map from a method to all transfer edges on the static graph that are associated with the method
	transient protected /*static*/ Map<Integer, List<DVTNode>> method2nodes;
	// a map from an edge type to all transfer edges of the type of the static graph
	transient protected /*static*/ Map<VTEdge.VTEType, List<DVTEdge>> type2edges;
	/** map from a node to all incoming edges */
	transient protected /*static*/ Map< DVTNode, Set<DVTEdge> > nodeToInEdges;
	
	/** a map from method signature to index for the underlying static VTG */
	transient protected /*static*/ Map< String, Integer > method2idx;
	/** a map from index to method signature for the underlying static VTG */
	transient protected /*static*/ Map< Integer, String > idx2method;
	
	/** a switch choosing whether to adopt the ReachingDefinition-style impact propagation, in which
	 *  a method A is regarded as impacted by method B only if there is some value defined by B reached some use of that value in A 
	 */
	static boolean reachingImpactPropagation = false;
	
	transient public Map<dua.util.Pair<Integer, String>, Map<Integer, Set<Integer>>> objIDMaps = null; 

	public DynTransferGraph() {
		super();
	}
	
	protected void initInternals() {
		super.initInternals();
		//if (null==svtg) svtg = new StaticTransferGraph();
		/*if (null==method2nodes)*/ method2nodes = new LinkedHashMap<Integer, List<DVTNode>>();
		/*if (null==type2edges)*/ type2edges = new LinkedHashMap<VTEType, List<DVTEdge>>();
		/*if (null==nodeToInEdges)*/ nodeToInEdges = new LinkedHashMap< DVTNode, Set<DVTEdge> >();
		method2idx = new LinkedHashMap<String, Integer>();
		idx2method = new LinkedHashMap<Integer, String>();
	}
	
	public void setTrace(String _fnTrace) {
		fnTrace = _fnTrace;
	}
	public void setSVTG(String _fnSVTG) {
		fnSVTG = _fnSVTG;
	}
	public Set<DVTEdge> getInEdges(DVTNode _node) { 
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
		
		this.method2idx.clear();
		this.idx2method.clear();
	}
	
	public void deepCopyFrom(DynTransferGraph vtg) { 
		this.clear();
	
		for (DVTEdge _e : vtg.edges) {
			this.createTransferEdge(_e.getSource().getVar(), _e.getSource().getMethod(), _e.getSource().getStmt(),
					_e.getTarget().getVar(), _e.getTarget().getMethod(), _e.getTarget().getStmt(), _e.getEdgeType());
		}
		
		this.classifyEdgeAndNodes();
	}
	
	private void classifyEdgeAndNodes() {
		// 1. build the method->VTG nodes map to facilitate edge activation and source-target matching later on
		/* list nodes by enclosing methods */
		for (DVTNode vn : nodes) {
			List<DVTNode> vns = method2nodes.get(vn.getMethod());
			if (vns == null) {
				vns = new LinkedList<DVTNode>();
				method2nodes.put(vn.getMethod(), vns);
			}
			vns.add(vn);
		}
		// 2. build the EdgeType->VTG edges map 
		for (DVTEdge edge : edges) {
			List<DVTEdge> els = type2edges.get(edge.getEdgeType());
			if (els == null) {
				els = new LinkedList<DVTEdge>();
				type2edges.put(edge.getEdgeType(), els);
			}
			els.add(edge);
		}
	}
	
	public void CopyFrom(DynTransferGraph vtg) {
		this.clear();
		super.CopyFrom(vtg);
		
		nodeToInEdges = vtg.nodeToInEdges;
		method2nodes = vtg.method2nodes;
		type2edges = vtg.type2edges;
		//this.classifyEdgeAndNodes();
	}
	
	@Override public int buildGraph(boolean debugOut) throws Exception{
		int index = 0;
		for (SVTNode sn : svtg.nodeSet()) {
			String mname = sn.getMethod().getName();
			if (!method2idx.containsKey(mname)) {
				method2idx.put(mname, index);
				idx2method.put(index, mname);
				index ++;
			}
		}
		for (SVTEdge se : svtg.edgeSet()) {
			createTransferEdge(
					utils.getCanonicalFieldName(se.getSource().getVar()),
					//utils.getFullMethodName(se.getSource().getMethod()),
					method2idx.get(se.getSource().getMethod().getName()),
					utils.getFlexibleStmtId(se.getSource().getStmt()),
					utils.getCanonicalFieldName(se.getTarget().getVar()),
					//utils.getFullMethodName(se.getTarget().getMethod()),
					method2idx.get(se.getTarget().getMethod().getName()),
					utils.getFlexibleStmtId(se.getTarget().getStmt()),
					se.getEdgeType());
		}
		return 0;
	}
	
	/** re-initialize the dynamic VTG starting from the static graph with coverage information applied
	 *  namely, prune nodes and edges associated with statements that are not covered according to the given covered list
	 */
	public int reInitializeGraph(StaticTransferGraph _svtg, List<Integer> coveredStmts) {
		int nPrunedEdges = 0;
		this.nodes.clear();
		this.edges.clear();
		this.nodeToEdges.clear();
		this.nodeToInEdges.clear();
		this.type2edges.clear();
		this.method2nodes.clear();
				
		for (SVTEdge se : _svtg.edgeSet()) {
			if (!coveredStmts.contains(utils.getFlexibleStmtId(se.getSource().getStmt())) || 
				 !coveredStmts.contains(utils.getFlexibleStmtId(se.getTarget().getStmt()))) {
				// prune an edge if either end-node is not covered
				nPrunedEdges++;
				continue;
			}
			
			createTransferEdge(
					utils.getCanonicalFieldName(se.getSource().getVar()),
					//utils.getFullMethodName(se.getSource().getMethod()),
					this.method2idx.get(se.getSource().getMethod().getName()),
					utils.getFlexibleStmtId(se.getSource().getStmt()),
					utils.getCanonicalFieldName(se.getTarget().getVar()),
					//utils.getFullMethodName(se.getTarget().getMethod()),
					this.method2idx.get(se.getTarget().getMethod().getName()),
					utils.getFlexibleStmtId(se.getTarget().getStmt()),
					se.getEdgeType());
		}
		
		classifyEdgeAndNodes();
		
		return nPrunedEdges;
	}
	
	/** as opposed to "pre-prune" non-covered nodes and edges they are incident to, as done by reInitialize(...), here is to
	 * prune non-covered members of the dynamic graph which has been exercised by the execution trace, for a given test case 
	 */
	public int postPruneByCoverage(DynTransferGraph dvtg, List<Integer> coveredStmts) {
		int nPrunedEdges = 0;
		
		for (DVTEdge de : this.edgeSet()) {
			if (!coveredStmts.contains(de.getSource().getStmt()) || 
					 !coveredStmts.contains(de.getTarget().getStmt())) {
					// prune an edge if either end-node is not covered
					nPrunedEdges++;
					continue;
			}
			
			dvtg.addEdge(de);
		}
		
		dvtg.classifyEdgeAndNodes();
		dvtg.method2idx = method2idx;
		dvtg.idx2method = idx2method;
		
		return nPrunedEdges;
	}
	/** prune nodes/edges of the dynamic graph that has already been exercised by the execution trace for a given test case, if
	 *  the source and target are not aliased to each other 
	 */
	public int postPruneByObjIDs(DynTransferGraph dvtg, Map<dua.util.Pair<Integer, String>, Set<Integer>> objIDs) {
		int nPrunedEdges = 0;
		
		for (DVTEdge de : this.edgeSet()) {
			dua.util.Pair<Integer, String> srcpair = new dua.util.Pair<Integer, String>(de.getSource().getStmt(), de.getSource().getVar());
			dua.util.Pair<Integer, String> tgtpair = new dua.util.Pair<Integer, String>(de.getTarget().getStmt(), de.getTarget().getVar());
			if (objIDs.get(srcpair)==null || objIDs.get(tgtpair)==null) {
				// no alias checking monitored at all
				dvtg.addEdge(de);
				continue;
			}
			
 			Set<Integer> srcset = new LinkedHashSet<Integer>(objIDs.get(srcpair));
 			srcset.retainAll(objIDs.get(tgtpair));
 			if (srcset.isEmpty())	{
				// prune an edge if the two end nodes are not dynamically aliased
				nPrunedEdges++;
				continue;
			}
			
			dvtg.addEdge(de);
		}
		
		dvtg.classifyEdgeAndNodes();
		dvtg.method2idx = method2idx;
		dvtg.idx2method = idx2method;
		
		return nPrunedEdges;
	}
	
	//public int nPrunedEdgeByObjID = 0;
	public final Set<DVTEdge> prunedByOID = new LinkedHashSet<DVTEdge>(); 
	protected boolean shouldPruneByObjID(DVTEdge de, Integer srcts, Integer tgtts) {
		dua.util.Pair<Integer, String> srcpair = new dua.util.Pair<Integer, String>(de.getSource().getStmt(), de.getSource().getVar());
		dua.util.Pair<Integer, String> tgtpair = new dua.util.Pair<Integer, String>(de.getTarget().getStmt(), de.getTarget().getVar());
		if (objIDMaps.get(srcpair)==null || objIDMaps.get(tgtpair)==null) {
			// no alias checking monitored at all
			return false;
		}
		
		if (objIDMaps.get(srcpair).get(srcts)==null || objIDMaps.get(tgtpair).get(tgtts)==null) {
			/*
			// no alias checking for the particular method occurrence monitored
			return false;
			*/
			// prune an edge if either of the two end nodes are not even executed at the particular method occurrence level
			prunedByOID.add(de);
			//nPrunedEdgeByObjID ++;
			return true;
		}
		
		Set<Integer> srcset = new LinkedHashSet<Integer>(objIDMaps.get(srcpair).get(srcts));
		srcset.retainAll(objIDMaps.get(tgtpair).get(tgtts));
		if (srcset.isEmpty())	{
			// prune an edge if the two end nodes are not dynamically aliased
			prunedByOID.add(de);
			//nPrunedEdgeByObjID ++;
			return true;
		}
		
		return false;
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
			EASeq = new LinkedHashMap<Integer, Integer>();
			EAMethodMap = new LinkedHashMap<Integer, String>();
		}
		else {
			EASeq.clear();
			EAMethodMap.clear();
		}
		FileInputStream fis;
		try {
			fis = new FileInputStream(fnSource);
			
			GZIPInputStream gis = new GZIPInputStream(fis);
			int len = 1024;
			int ziplen = (int)new File(fnSource).length();
			byte[] bs = new byte[ziplen*20]; // Gzip won't have more than 20 compression ratio for the binary data
			int off = 0;
			while (gis.available()!=0) {
				off += gis.read(bs, off, len);
			}
			gis.close();
			fis.close();

			ByteArrayInputStream bis = new ByteArrayInputStream(bs);
			
			//ObjectInputStream ois = new ObjectInputStream(fis);
			ObjectInputStream ois = new ObjectInputStream(bis);
			
			Map<String,Integer> EAmethod2idx = new LinkedHashMap<String,Integer>();
			@SuppressWarnings("unchecked")
			LinkedHashMap<String,Integer> readObject1 = (LinkedHashMap<String,Integer>) ois.readObject();
			EAmethod2idx = readObject1;
			for (Map.Entry<String, Integer> en : EAmethod2idx.entrySet()) {
				// create an inverse map for facilitating quick retrieval later on
				EAMethodMap.put(en.getValue(), en.getKey());
			}
			
			@SuppressWarnings("unchecked")
			LinkedHashMap<Integer, Integer> readObject2 = (LinkedHashMap<Integer, Integer>) ois.readObject();
			EASeq = readObject2;
			
			ois.close();
			bis.close();
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
		
	protected void createTransferEdge(DVTNode src, DVTNode tgt, VTEType etype) {
		DVTEdge edge = new DVTEdge(src, tgt, etype);
		if (!edges.contains(edge)) {
			addEdge(edge);
		}
	}
	
	/** avoid creating redundant instances of a same node */ 
	private DVTNode getCreateDVTNode(String var, Integer method, Integer stmt) {
		DVTNode ret = new DVTNode(var, method, stmt);
		if (nodes.contains(ret)) {
			for (DVTNode n : nodes) {
				if (n.equals(ret)) {
					return n;
				}
			}
			assert false;
		}
		return ret;
	}

	/** a convenient routine for adding an edge and the covered nodes into the graph */
	private void createTransferEdge(String srcVar, Integer srcMethod, Integer srcStmt,
						String tgtVar, Integer tgtMethod, Integer tgtStmt, VTEType etype) {
		// TODO:
		// any transfer edges associated with methods unreachable from entry should be ignored

		DVTNode src = /*new DVTNode*/getCreateDVTNode(srcVar, srcMethod, srcStmt);
		DVTNode tgt = /*new DVTNode*/getCreateDVTNode(tgtVar, tgtMethod, tgtStmt);
	
		createTransferEdge(src, tgt, etype);
	}
	
	public void addEdge(DVTEdge edge) {
		if (edges.contains(edge)) return;
		DVTNode src = edge.getSource(), tgt = edge.getTarget();
		
		nodes.add(src);
		nodes.add(tgt);
		edges.add(edge);
		
		Set<DVTEdge> outEdges = nodeToEdges.get(src);
		if (null == outEdges) {
			outEdges = new HashSet<DVTEdge>();
		}
		outEdges.add(edge);
		nodeToEdges.put(src, outEdges);
		
		Set<DVTEdge> inEdges = nodeToInEdges.get(tgt);
		if (null == inEdges) {
			inEdges = new HashSet<DVTEdge>();
		}
		inEdges.add(edge);
		nodeToInEdges.put(tgt, inEdges);
	}
	
	/**
	 * Create a dynamic transfer graph by first loading the static graph and then pruning edges according to the given
	 * execution trace;
	 * Without giving an origin of change, this intends to build a dynamic transfer graph for any later queries
	 */
	public int buildGraph(DynTransferGraph ndvtg, boolean debugOut) throws Exception{
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
		
		// for different types of edges, we have different strategies for edge activation and source-target matching, so we maintain
		// a list of open source nodes for each edge type
		Map< VTEType, Set<DVTNode> > openNodes = new HashMap<VTEType, Set<DVTNode>>();
		for (VTEType etype : VTEType.values() /*type2edges.keySet()*/ ) {
			openNodes.put(etype, new LinkedHashSet<DVTNode>());
		}
		
		// the temporary dynamic VTG that keeps activated transfer edges only, will eventually substitute "this" dynamic graph
		DynTransferGraph dvtg = ndvtg; //new DynTransferGraph();
		Integer preMethod = null;
				
		int g_traceCnt = 0;
		while (true) {
			
			String curfnTrace = fnTrace + (g_traceCnt>0?g_traceCnt:"");
			if (!new File(curfnTrace).exists()) {
				// all segments have been processed
				break;
			}
			g_traceCnt ++;
			
			if (0 != loadEASequence(curfnTrace/*fnTrace*/)) {
				// trace not loaded successfully
				return -3;
			}
				
			// - For DEBUG only
			if (debugOut) {
				System.out.println("===== method indexing map =====");
				System.out.println(EAMethodMap);
				System.out.println("===== The current execution trace under use [loaded from the call sequence] =====");
				TreeMap<Integer, Integer> treeA = new TreeMap<Integer, Integer> ( EASeq );
				System.out.println(treeA);
			}
			
			// 3. scan the execution trace and activate transfer edges
			for (Map.Entry<Integer, Integer> _event : EASeq.entrySet()) {
				Integer va = _event.getValue();
				//if (va.equalsIgnoreCase("program start") || va.equalsIgnoreCase("program end")) {
				if (va == Integer.MIN_VALUE || va == Integer.MAX_VALUE) {
					// these are just two special events marking start and termination of the run
					continue;
				}
				/*
				int endIdx = va.lastIndexOf(":");
				// get the class and method name 
				assert endIdx >= 0;
				String em = _event.getValue().substring(0, endIdx);
				// get the event type: enter or return
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
				*/
				Integer em = method2idx.get(EAMethodMap.get(Math.abs(va)));
				boolean isEnterEvent = va < 0;
							
				// check each of all nodes associated with the currently checked method
				if (em==null || method2nodes.get(em) == null) {
					//System.out.println("associated with no nodes: " + em);
					continue;
				}
				for (DVTNode _n : method2nodes.get(em)) {
					// attach the event's time stamp to the dynamic VTG node
					_n.setTimestamp(_event.getKey());
					
					if (isEnterEvent) {
						// examine each of all the outgoing edges from the node
						Set<DVTEdge> oedges = getOutEdges(_n);
						if (null != oedges) {
							for (DVTEdge _e : oedges) {
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
						Set<DVTEdge> iedges = getInEdges(_n);
						if (iedges != null) {
							for (DVTEdge _e : iedges) {
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
						Set<DVTEdge> oedges = getOutEdges(_n);
						if (null != oedges) {
							for (DVTEdge _e : oedges) {
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
						Set<DVTEdge> iedges = getInEdges(_n);
						if (null != iedges) {
							for (DVTEdge _e : iedges) {
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
				for (Map.Entry< VTEType, Set<DVTNode> > _en : openNodes.entrySet()) {
					if ( ! (_en.getKey().equals(VTEType.VTE_PARAM) || _en.getKey().equals(VTEType.VTE_PARARET) ||
							_en.getKey().equals(VTEType.VTE_RET)) ) {
						// close nodes for "adjacent type" edges only
						continue;
					}
					Set<DVTNode> toRemove = new HashSet<DVTNode>();
					for (DVTNode _n : _en.getValue()) {
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
		} // for each trace segment
		
		// now, update the graph to the really dynamic one
		/*
		this.CopyFrom(dvtg);
		this.classifyEdgeAndNodes();
		*/
		dvtg.classifyEdgeAndNodes();
		// these two maps are the same between the static and dynamic VTG since when we are using the indices for
		// methods we refer to the same global index map, which is unique for each static VTG
		dvtg.method2idx = method2idx;
		dvtg.idx2method = idx2method;
		
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
		for (Integer _m : method2nodes.keySet()) {
			String mn = idx2method.get(_m);
			if (mn.toLowerCase().contains(chg.toLowerCase())) {
				chgSet.add(mn);
			}
		}
		return chgSet;
	}
	
	private void getImpactSetImpl(DVTNode start, Set<DVTNode> visited, Set<String> mis) {
		if (!visited.add(start)) {
			return;
		}
		mis.add( idx2method.get(start.getMethod()) );
		if (null == getOutEdges(start)) return;
		
		// find the incoming edge with maximal time stamp at its starting point
		int mts = Integer.MIN_VALUE;
		if (reachingImpactPropagation) {
			if (getInEdges(start) != null) {
				for (DVTEdge _in : getInEdges(start)) {
					mts = Math.max(mts, _in.getSource().getTimestamp());
				}
			}
		}
		for (DVTEdge _e : getOutEdges(start)) {
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
		/** No! if it is never executed or statically never called, it should not be */
		//mis.add(chgm);
		
		Integer chgmIdx = method2idx.get(chgm);
		assert chgmIdx!=null;
		
		Set<DVTNode> visited = new LinkedHashSet<DVTNode>();
		List<DVTNode> startNodes = method2nodes.get(chgmIdx);
		if (startNodes != null) {
			for (DVTNode _n : startNodes) {
				getImpactSetImpl(_n, visited, mis);
			}
		}
				
		return mis;
	}
	
	/** a helper function, initialize the set of affected nodes by the given chgm, for 
	 * public Set<String> buildGraph(String chgm, boolean debugOut)
	 * namely, collect all directly reachable methods from chgm
	 */ 
	private void initAffectedNodes(Map<VTEType, Set<DVTNode>> nodes, VTEType etype, Integer chgm) {
		for (DVTNode _n : method2nodes.get(chgm)) {
			if (this.getOutEdges(_n) != null) {
				for (DVTEdge _e : this.getOutEdges(_n)) {
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
	private void updateAffectedNodes(Map<VTEType, Set<DVTNode>> nodes, VTEType etype, Integer curm) {
		Set<DVTNode> nset = nodes.get(etype);
		if (nset == null || nset.isEmpty()) {
			// nothing to update
			return;
		}
		Set<DVTNode> _nset = new LinkedHashSet<DVTNode>(); // the new affected set
		for (DVTNode _n : nset) {
			if (this.getOutEdges(_n) != null) {
				for (DVTEdge _e : this.getOutEdges(_n)) {
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
	public int buildGraph(DynTransferGraph ndvtg, String chgm, boolean debugOut) {
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
		
		/** for different types of edges, we have different strategies for edge activation and source-target matching, so we maintain
		 * a list of open source nodes for each edge type
		 */
		Map< VTEType, Set<DVTNode> > openNodes = new HashMap<VTEType, Set<DVTNode>>();
		/** also, since we already know the query, we could record a propagation "flag" for each of the type of edge:
		 * more precisely, for Type 1 (Local) edges, the flag is always False, and for Type 3 (Heap object edges) it is always True;
		 * for Type 2 (one-method away, including parameterEdge, returnEdge and RefParamEdge) edges, the flag should be updated
		 * during the traversal according to the consecutive order in regard of the edge source method and edge target method
		 */
		Map<VTEType, Boolean> propFlags = new HashMap<VTEType, Boolean>();
		/** And, nodes to which the change from the origin (the query) has been propagated so far are recorded for deciding if we should
		 * mark nodes open, for each of the AdjacentEdges
		 */
		Map<VTEType, Set<DVTNode>> affectedNodes = new HashMap<VTEType, Set<DVTNode>>();
		for (VTEType etype : VTEType.values() /*type2edges.keySet()*/ ) {
			openNodes.put(etype, new LinkedHashSet<DVTNode>());
			/** Heap objects propagate changes across any number of intermediate methods if there is any edge connecting through*/
			propFlags.put(etype, !VTEdge.isAdjacentType(etype));
			affectedNodes.put(etype, new LinkedHashSet<DVTNode>());
		}
		/* 
		propFlags.put(VTEType.VTE_STVAR, true);
		propFlags.put(VTEType.VTE_INSVAR, true);
		propFlags.put(VTEType.VTE_ARRAYELE, true);
		*/
		
		// the temporary dynamic VTG that keeps activated transfer edges only, will eventually substitute "this" dynamic graph
		DynTransferGraph dvtg = ndvtg; //new DynTransferGraph();
		Integer preMethod = null;
		Integer chgmIdx = method2idx.get(chgm);
		assert chgmIdx != null;
		
		// mark the first enter event of the change method
		boolean bChgEnter = false;
		
		// to handle multiple-file trace for a single test case
		int g_traceCnt = 0;
		while (true) {
			
			String curfnTrace = fnTrace + (g_traceCnt>0?g_traceCnt:"");
			if (!new File(curfnTrace).exists()) {
				// all segments have been processed
				break;
			}
			g_traceCnt ++;
			
			//if (0 != loadEASequence(fnTrace)) {
			if (0 != loadEASequence(curfnTrace)) {
				// trace not loaded successfully
				return -3;
			}
			
			// - For DEBUG only
			if (debugOut) {
				System.out.println("===== method indexing map =====");
				System.out.println(EAMethodMap);
				System.out.println("===== The current execution trace under use [loaded from the call sequence] =====");
				TreeMap<Integer, Integer> treeA = new TreeMap<Integer, Integer> ( EASeq );
				System.out.println(treeA);
			}
			
			// 3. scan the execution trace and activate transfer edges
	
			for (Map.Entry<Integer, Integer> _event : EASeq.entrySet()) {
				Integer va = _event.getValue();
				//if (va.equalsIgnoreCase("program start") || va.equalsIgnoreCase("program end")) {
				if (va == Integer.MIN_VALUE || va == Integer.MAX_VALUE) {	
					// these are just two special events marking start and termination of the run
					continue;
				}
				/*
				int endIdx = va.lastIndexOf(":");
				// get the class and method name
				assert endIdx >= 0;
				String em = _event.getValue().substring(0, endIdx);
				*/
				String emstr = EAMethodMap.get(Math.abs(va));
				Integer em = method2idx.get(emstr);
				
				if (!bChgEnter) {
					// em includes the class name and method name, together giving the origin of change
					bChgEnter = chgmIdx.equals(em);
					if (!bChgEnter) {
						// methods occurred before the first enter of the change method won't be impacted by the change mehtod 
						continue;
					}
				}
				/*
				// get the event type: enter or return
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
				*/
				boolean isEnterEvent = va < 0;
							
				// check each of all nodes associated with the currently checked method
				if (em==null || method2nodes.get(em) == null) {
					//System.out.println("associated with no nodes: " + em);
					continue;
				}
				
				// update the "propagation flags" per currently encountered method
				for (VTEType etype : VTEType.values()/*type2edges.keySet()*/ ) {
					if (VTEdge.isAdjacentType(etype)) {
						// start or stop propagating change impact via Adjacent edges, depending on it the chgm occurred					
						propFlags.put(etype, /*isEnterEvent &&*/ chgmIdx.equals(em));
					}
				}
				
				//if (isEnterEvent) {
					if (propFlags.get(VTEType.VTE_PARAM)) {
						initAffectedNodes(affectedNodes, VTEType.VTE_PARAM, chgmIdx);
					}
					else {
						updateAffectedNodes(affectedNodes, VTEType.VTE_PARAM, em);
					}
					
					if (propFlags.get(VTEType.VTE_RET)) {
						initAffectedNodes(affectedNodes, VTEType.VTE_RET, chgmIdx);
					}
					else {
						updateAffectedNodes(affectedNodes, VTEType.VTE_RET, em);
					}
					
					if (propFlags.get(VTEType.VTE_PARARET)) {
						initAffectedNodes(affectedNodes, VTEType.VTE_PARARET, chgmIdx);
					}
					else {
						updateAffectedNodes(affectedNodes, VTEType.VTE_PARARET, em);
					}/*
				}
				else {
					updateAffectedNodes(affectedNodes, VTEType.VTE_RET, em);
					updateAffectedNodes(affectedNodes, VTEType.VTE_PARARET, em);
				}*/
				
				for (DVTNode _n : method2nodes.get(em)) {
					// attach the event's time stamp to the dynamic VTG node
					_n.setTimestamp(_event.getKey());
					
					if (isEnterEvent) {
						// examine each of all the outgoing edges from the node
						Set<DVTEdge> oedges = getOutEdges(_n);
						if (null != oedges) {
							for (DVTEdge _e : oedges) {
								// 1. local edges, all to be activated once the hosting method got executed
								if (_e.isLocalEdge()) {
									// dynamic alias checking based pruning
									if (objIDMaps!=null && shouldPruneByObjID(_e, _event.getKey(), _event.getKey())) { continue; }
									
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
						Set<DVTEdge> iedges = getInEdges(_n);
						if (iedges != null) {
							for (DVTEdge _e : iedges) {
								// 1. local edges, all to be activated once the hosting method got executed
								if (_e.isLocalEdge()) {
									// dynamic alias checking based pruning
									if (objIDMaps!=null && shouldPruneByObjID(_e, _event.getKey(), _event.getKey())) { continue; }
									
									dvtg.addEdge(_e);
									continue;
								}
								
								// 2. Heap object edges and parameter edges are activated upon the matching of the target with "open" source
								if (_e.isParameterEdge() || _e.isHeapEdge()) {
									// match open source for the target
									if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
										// dynamic alias checking based pruning
										if (objIDMaps!=null && shouldPruneByObjID(_e, _e.getSource().getTimestamp(), _event.getKey())) { continue; }
										
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
						Set<DVTEdge> oedges = getOutEdges(_n);
						if (null != oedges) {
							for (DVTEdge _e : oedges) {
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
						Set<DVTEdge> iedges = getInEdges(_n);
						if (null != iedges) {
							for (DVTEdge _e : iedges) {
								// 1. Local edges: have already been added when processing the enter event of the relevant methods
								
								// 2. Return edges follow the same rule of matching as the RefParam edges since the latter can be essentially
								//     regarded as a kind of Return;
								// And, heap object edges can also transfer changes from callee to caller
								if (_e.isReturnEdge() || _e.isRefReturnParamEdge() || _e.isHeapEdge()) {
									if ( openNodes.get(_e.getEdgeType()).contains( _e.getSource() )) {
										// dynamic alias checking based pruning
										if (objIDMaps!=null && shouldPruneByObjID(_e, _e.getSource().getTimestamp(), _event.getKey())) { continue; }
										
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
				for (Map.Entry< VTEType, Set<DVTNode> > _en : openNodes.entrySet()) {
					//if ( ! (_en.getKey().equals(VTEType.VTE_PARAM) || _en.getKey().equals(VTEType.VTE_PARARET) ||	_en.getKey().equals(VTEType.VTE_RET)) ) {
					/** Interprocedural CD edges can pass across any number of methods, like Heap object transfer edges */
					if ( !VTEdge.isAdjacentType(_en.getKey()) /*&& !ValueTransferGraph.isControlType(_en.getKey()) */) {
						// close nodes for "adjacent type" edges only
						continue;
					}
					Set<DVTNode> toRemove = new HashSet<DVTNode>();
					for (DVTNode _n : _en.getValue()) {
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
		} // for each trace segment file
		
		// now, update the graph to the really dynamic one
		/*
		this.CopyFrom(dvtg);
		this.classifyEdgeAndNodes();
		*/
		ndvtg.classifyEdgeAndNodes();
		// these two maps are the same between the static and dynamic VTG since when we are using the indices for
		// methods we refer to the same global index map, which is unique for each static VTG
		dvtg.method2idx = method2idx;
		dvtg.idx2method = idx2method;
		
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
	public int pruneGraph(DynTransferGraph ndvtg, boolean debugOut) {
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
		
		// index methods appeared in the current execution trace
		List<Integer> methodInSeq = new ArrayList<Integer>();
		List<Boolean> eventTypeInSeq = new ArrayList<Boolean>();
	
		// to handle multiple-file trace for a single test case
		int g_traceCnt = 0;
		while (true) {
			
			String curfnTrace = fnTrace + (g_traceCnt>0?g_traceCnt:"");
			if (!new File(curfnTrace).exists()) {
				// all segments have been processed
				break;
			}
			g_traceCnt ++;
			
			if (0 != loadEASequence(curfnTrace/*fnTrace*/)) {
				// trace not loaded successfully
				return -3;
			}
			
			// - For DEBUG only
			if (debugOut) {
				System.out.println("===== method indexing map =====");
				System.out.println(EAMethodMap);
				System.out.println("===== The current execution trace under use [loaded from the call sequence] =====");
				TreeMap<Integer, Integer> treeA = new TreeMap<Integer, Integer> ( EASeq );
				System.out.println(treeA);
			}
			
			/*
			// before pruning, make a clone of the initial dvtg, which will be reused by later execution traces
			ndvtg.deepCopyFrom(this);
			*/
					
			for (Map.Entry<Integer, Integer> _event : EASeq.entrySet()) {
				Integer va = _event.getValue();
				//if (va.equalsIgnoreCase("program start") || va.equalsIgnoreCase("program end")) {
				if (va == Integer.MIN_VALUE || va == Integer.MAX_VALUE) {
					// these are just two special events marking start and termination of the run
					continue;
				}
				/*
				int endIdx = va.lastIndexOf(":");
				// get the class and method name
				assert endIdx >= 0;
				String em = _event.getValue().substring(0, endIdx);
				
				// get the event type: enter or return
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
				*/
				Integer em = method2idx.get(EAMethodMap.get(Math.abs(va)));
				boolean isEnterEvent = va < 0;
				
				methodInSeq.add(em);
				eventTypeInSeq.add(isEnterEvent);
			}
		} // for each trace segment	
			
		Set<DVTEdge> toPrune = new LinkedHashSet<DVTEdge>();
		
		// 3. prune edges containing nodes whose associated method is never executed
		for (DVTEdge _e : edges) {
			if ( !methodInSeq.contains(_e.getSource().getMethod()) || !methodInSeq.contains(_e.getTarget().getMethod()) ) {
				toPrune.add(_e);
			}
		}
		
		// 4. prune parameter edges whose source is never immediately followed by the target in the trace
		for (DVTEdge _e : edges) {
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
		for (DVTEdge _e : edges) {
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
		for (DVTEdge _e : edges) {
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
		for (DVTEdge _e : edges) {
			if (!toPrune.contains(_e)) {
				ndvtg.addEdge(_e);
			}
		}
				
		ndvtg.classifyEdgeAndNodes();
		// these two maps are the same between the static and dynamic VTG since when we are using the indices for
		// methods we refer to the same global index map, which is unique for each static VTG
		ndvtg.method2idx = method2idx;
		ndvtg.idx2method = idx2method;
		
		return 0;
	}
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	@Override public DynTransferGraph DeserializeFromFile(String sfn) {
		Object o = super.DeserializeFromFile(sfn);
		if (o != null) {
			DynTransferGraph vtg = new DynTransferGraph();
			vtg = (DynTransferGraph)o;
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
		
		System.out.println("---------- method indexing map -------------");
		for (Map.Entry<Integer, String> en : idx2method.entrySet()) {
			System.out.println(en.getKey() + " : " + en.getValue());
		}
		
		for (Map.Entry<Integer, List<DVTNode>> en : method2nodes.entrySet()) {
			System.out.println("----------------------------------------- " + 
					idx2method.get(en.getKey()) + " [" +	en.getValue().size() + 
					" nodes] -----------------------------------------");
			for (DVTNode vn : en.getValue()) {
				System.out.println("\t"+vn);
			}
		}
		
		/* list edges by types */
		for (Map.Entry<VTEType, List<DVTEdge>> en : type2edges.entrySet()) {
			System.out.println("----------------------------------------- " + 
					VTEdge.edgeTypeLiteral(en.getKey()) + " [" +	en.getValue().size() + 
					" edges] -----------------------------------------");
			for (DVTEdge edge : en.getValue()) {
				System.out.println("\t"+edge);
			}
		}
		return 0;
	}
} // definition of DynTransferGraph

/* vim :set ts=4 tw=4 tws=4 */
