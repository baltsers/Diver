/**
 * File: src/Diver/StaticCDGraphEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created; model a static exceptional control dependence graph
 * 03/28/14		hcai		fixed inconsiderate assertions in makeSymbolicCDEdge 
*/
package Diver;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import dua.global.ProgramFlowGraph;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.NodeDefUses;
import dua.method.CFGDefUses.StdVariable;
import dua.method.CFGDefUses.Variable;
import dua.method.CallSite;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.ExceptionalUnitGraph;

import MciaUtil.*;
import MciaUtil.VTEdge.VTEType;
import MciaUtil.CompleteUnitGraphEx.*;

/**
 * The static Exceptional Control Dependence Graph constructed using the ExceptionUnitGraph with lax throw analysis, and
 * with implicit exceptional edges omitted; 
 * The edge and node components follow the same type as those used in the VTG but are involved with CD edges only; this
 * graph can be merged into VTG by simply adding the CD edges to VTG to become one of the various types of edges, for
 * computing change impact propagations.
 */
public class StaticCDGraphEx extends ControlDependenceEx<SVTNode, SVTEdge> {
	/** Set of definitions initialized by formal parameters and static/instance variable writers, 
	 * specific to a particular method 
	 */ 
	private List<SVTNode> curDefSet = null;
	
	/** Set of CD source stmt, as have no defs, for which the <b>intraprocedural valute transfer edges</b> have 
	 * been created, which connect each of all definitions (still, we are in the flow-insensitive approach) of 
	 * each used var to the var there  
	 */
	private final Set<Stmt> connectedCDSrcs = new LinkedHashSet<Stmt>();
	
	/**
	 * In constructing the per-CFG reduced CDG, we care only, at least for now, about the CD edges at such 
	 * granularity that both vertices are in the minimal unit of statement, and we use the symbolic "variable"
	 * only for adapting to the "SVTNode" structure hence the variable is just a place holder!
	 * Therefore, we don't need to distinguish the variables used for different types of statements on the CD edge
	 */
	public static class SymbolicCDSource {
		public static int SCDS_ENTRY = 0;//10; 			// ENTRY
		public static int SCDS_TRUEBRANCH = 0;//1; // true branch of a decision vertex
		public static int SCDS_FALSEBRANCH = 0;//0; // false branch of a decision vertex
		public static int SCDS_FALLTHROUGH = 0;//0; // ordinary falls-through
		public static int SCDS_RETURN = 0;//3;			  // return stmt at CD source
		public static int SCDS_OTHER = 0;//4; 			// all other types we don't want to distinguish
	};
	public static class SymbolicCDTarget {
		public static int SCDT_NORMAL = 0;//-1; // all CD targets that are real stmts
		public static int SCDT_EXIT = 0;//-10; 		// EXIT
		public static int SCDT_OTHER = 0;//4; 	// all other types we don't want to distinguish
	};
	
	public StaticCDGraphEx (boolean debugOut) {
		super(debugOut);
	}
	public StaticCDGraphEx () {
		super();
	}
	
	public void setCurDefSet(List<SVTNode> curset) {
		curDefSet = curset;
	}
	
	public static SVTEdge makeSymbolicCDEdge(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts) {
		Variable srcv = null;
		if (srcs.getUnitBoxes().size() >= 1) {
			int tgtIdx = utils.isUnitInBoxes(srcs.getUnitBoxes(), tgts);
			if (tgtIdx>=0) {
				/** target index (1 for IfStmt, namely the true branch) */
				srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_TRUEBRANCH/*tgtIdx+1*/));	
			}
			else {
				assert srcs.branches();
				if (srcs.fallsThrough()) {
					/** fall through (0 for IfStmt, namely the false branch) */
					srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_FALSEBRANCH));
				}
				else {
					/** fall through for other types of branch statement */
					srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_FALSEBRANCH));
				}
			}
		}
		else {
			if (srcs instanceof AugmentedUnit) {
				/** Virtual node: ENTRY */
				assert /*srcs == CompleteUnitGraphEx.ENTRY*/CompleteUnitGraphEx.isEntry(srcs);
				srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_ENTRY));
			}
			else if (srcs.fallsThrough()) {
				/** ordinary sequential fall-through */
				srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_FALLTHROUGH));
			}
			else {
				//assert false;
				/** Returns */
				// assert dua.util.Util.isReturnStmt(srcs);
				// srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_RETURN));
				if (dua.util.Util.isReturnStmt(srcs)) {
					srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_RETURN));
				}
				else {
					srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_OTHER));
				}
			}
		}
		SVTNode srcn = new SVTNode( srcv, srcm, srcs );
		
		Variable tgtv = null;
		if (tgts instanceof AugmentedUnit) {
			/** Virtual node: EXIT */
			assert /*tgts == CompleteUnitGraphEx.EXIT*/CompleteUnitGraphEx.isExit(tgts);
			tgtv = new StdVariable(IntConstant.v(SymbolicCDTarget.SCDT_EXIT));
		}
		else {
			/** all other symbolic CD targets */
			tgtv = new StdVariable(IntConstant.v(SymbolicCDTarget.SCDT_NORMAL)); // a dummy variable just for compatibility of SVTNode constructor
		}
		SVTNode tgtn = new SVTNode( tgtv, tgtm, tgts );
		SVTEdge e = null;
		if (srcm.equals(tgtm)) {
			e = new SVTEdge(srcn, tgtn, VTEType.VTE_CONTROL_INTRA);
		}
		else {
			e = new SVTEdge(srcn, tgtn, VTEType.VTE_CONTROL_INTER);
		}
		
		return e;
	}
	
	/** create a control transfer edge from the CD edge source to control edge target, using a symbolic variable as the place-holder
	 *   for the "variable" field of VTG node
	 */
	protected Set<SVTEdge> createSymbolicCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts) {
		Set<SVTEdge> _edges = new LinkedHashSet<SVTEdge>();
		/*
		NodeDefUses srcNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(srcs);
		NodeDefUses tgtNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(tgts);
		for (Variable srcv : srcNdu.getDefinedVars()) {
			for (Variable tgtv : tgtNdu.getDefinedVars()) {
				
				SVTNode srcn = new SVTNode( new StdVariable(srcv.getValue()), srcm, srcs );
				SVTNode tgtn = new SVTNode( new StdVariable(tgtv.getValue()), tgtm, tgts );
				addEdge(new SVTEdge(srcn, tgtn, VTEType.VTE_CONTROL));
			}
		}
		*/
		
		/*
		NodeDefUses tgtNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(tgts);
		if (tgtNdu.getDefinedVars().size() < 1) {
			Variable tgtv = new StdVariable(IntConstant.v(-1)); // a dummy variable just for compatibility of SVTNode constructor
			
			SVTNode tgtn = new SVTNode( tgtv, tgtm, tgts );
			SVTEdge e = new SVTEdge(srcn, tgtn, VTEType.VTE_CONTROL_INTRA);
			addEdge(e);
			edges.add(e);
		}
		else {
			for (Variable tgtv : tgtNdu.getDefinedVars()) {
				
				SVTNode tgtn = new SVTNode( new StdVariable(StringConstant.v(tgtv.toString())), tgtm, tgts );
				SVTEdge e = new SVTEdge(srcn, tgtn, VTEType.VTE_CONTROL_INTRA);
				addEdge(e);
				edges.add(e);
			}
		}
		*/
		SVTEdge e = makeSymbolicCDEdge(srcm, srcs, tgtm, tgts);
		addEdge(e);
		_edges.add(e);
		
		return _edges;
	}
	
	/** A helper function that creates a CDEdgeVar for a statement that has no defined variables */
	public static CDEdgeVar makeCDEdgeVar(CFGNode n) {
		Stmt s = n.getStmt();
		CDEdgeVar cdsv = null;
		if (s instanceof IfStmt) {
			IfStmt is = (IfStmt)s;
			assert is.getCondition() instanceof ConditionExpr;
			ConditionExpr ce = (ConditionExpr)is.getCondition();
			cdsv = new CDEdgeVar(ce, n);
		}
		else if (s instanceof InvokeStmt) {
			cdsv = new CDEdgeVar(((InvokeStmt)s).getInvokeExpr(), n);
		}
		else if (s instanceof LookupSwitchStmt) {
			cdsv = new CDEdgeVar(((LookupSwitchStmt)s).getKey(), n);
		}
		else if (s instanceof MonitorStmt) {
			cdsv = new CDEdgeVar( ((MonitorStmt)s).getOp(), n ); 
		}
		else if (s instanceof RetStmt) {
			cdsv = new CDEdgeVar( ((RetStmt)s).getStmtAddress(), n);
		}
		else if (s instanceof ReturnStmt) {
			cdsv = new CDEdgeVar( ((ReturnStmt)s).getOp(), n);
		}
		else if (s instanceof TableSwitchStmt) {
			cdsv = new CDEdgeVar( ((TableSwitchStmt)s).getKey(), n ); 
		}
		else if (s instanceof ThrowStmt) {
			cdsv = new CDEdgeVar( ((ThrowStmt)s).getOp(), n ); 
		}
		else if (s instanceof GotoStmt) {
			cdsv = new CDEdgeVar(StringConstant.v( ((GotoStmt)s).getTarget().toString()), n);
		}
		else if (s instanceof ReturnVoidStmt) {
			cdsv = new CDEdgeVar(StringConstant.v("Void Return"), n);
		}
		else {
			// what is missing?
			assert false;
			cdsv = new CDEdgeVar(StringConstant.v(s.toString()), n);
		}
		return cdsv;
	}
	
	/** Derive a set of VTG-compatible edges from a single symbolic (statement to statement) level CD edge
	 * more precisely, create a full set of control transfer edges from each of the defined variable, if any, 
	 * at the CD edge source to each defined variable, if any, at the control edge target;
	 * 
	 *  if the source or target has no any defs, SVTNode for the corresponding vertex at the CD edge will be created using a 
	 *  CDEdgeVar variable wherein the underlying Value is hosted using that variable  
	 */
	protected Set<SVTEdge> createFullCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts) {
		Set<SVTEdge> _edges = new LinkedHashSet<SVTEdge>();
		/*
		if (srcs instanceof IfStmt) {
			IfStmt isrc = (IfStmt)srcs;
			assert isrc.getCondition() instanceof ConditionExpr;
			ConditionExpr ce = (ConditionExpr)isrc.getCondition();
			ValueBox vb = isrc.getConditionBox();
			NodeDefUses srcNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(srcs);
			List<Variable> defsAtSrc = srcNdu.getDefinedVars();
			assert defsAtSrc.size()==0;
		}
		else {
			System.out.println("Non IfStmt CD edge source: " + srcs);
			NodeDefUses srcNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(srcs);
			List<Variable> defsAtSrc = srcNdu.getDefinedVars();
			assert defsAtSrc.size()>=1;
		}
		*/
		
		// for the "virtual node" such as ENTRY and EXIT, it is pointless to merge them into the value transfer graph where we 
		// only model value/control transfers between REAL program entities (real statements and real Values at those statements)  
		if ( srcs instanceof AugmentedUnit || tgts instanceof AugmentedUnit) {
			return _edges;
		}
		
		Set<SVTNode> allSrcs = new LinkedHashSet<SVTNode>();
		
		NodeDefUses srcNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(srcs);
		List<Variable> defsAtSrc = srcNdu.getDefinedVars();
		if (defsAtSrc.size() < 1) {
			/** model a CDEdgeVar variable for such CD source in order to create a SVTNode for it */
			Variable srcVar = makeCDEdgeVar(srcNdu);
			SVTNode srcNode = new SVTNode(StaticTransferGraph.varAbstraction(srcVar, srcm), srcm, srcs);
			allSrcs.add(srcNode);

			/** to "joint" the CD edges to be created to the Value transfer graph, we need first connect the defs of used vars at the
			 * CD source if the source does not have any defined variable nor is app call site, for which we did not create any value
			 * transfer edges reaching the location (statement) 
			 * 
			 * Recall that in the value transfer graph, intraprocedural value transfer edges only care about connecting def to def, 
			 * with only one exception : the app call site, handled by StaticTransferGraph::createLocalEdgesForCallSite
			 * Now, we have another exception here, namely the CD edge source having no defs nor is an app call site
			 * 
			 * However, "StaticTransferGraph::createLocalEdgesForCallSite" connects from defs to uses rather than defs to the
			 * CDEdgeVar, which is what we need here. So regardless of having app call site or not, we need create edges from each
			 * of the defs of each use at srcs to the monolithic CDEdgeVar modeled above 
			 */
			if (connectedCDSrcs.add(srcs) /*&& (srcNdu.getCallSite()==null || !srcNdu.hasAppCallees())*/) {
				List<Variable> usesAtSrc = srcNdu.getUsedVars();
				for (Variable usrc : usesAtSrc) {
					Set<SVTNode> defs4use = StaticTransferGraph.getAllDefs(this.curDefSet, usrc, srcm, srcNdu);
					for (SVTNode dn : defs4use) {
						if ( (usrc.isArrayRef() && dn.getVar().isArrayRef())  || (usrc.isFieldRef() && dn.getVar().isFieldRef()) || 
								(usrc.isObject() && dn.getVar().isObject()) ) {
							if (!srcm.equals(dn.getMethod())) {
								// we care about intraprocedural defs only to avoid redundant edges - we already have 
								// interprocedural value transfer edges connecting writers to readers of ArrayRefs, FieldRefs and LibObjs 
								continue;
							}
						}
						
						SVTEdge e = new SVTEdge(dn, srcNode, VTEType.VTE_INTRA);
						addEdge(e);
						//_edges.add(e); // _edges is only used for recording which CD edges are created
					} // for each def of a use at the CD source
				} // for each use at the CD source
			}
		}
		else {
			for (Variable dsrc : defsAtSrc) {
				SVTNode srcNode = new SVTNode(StaticTransferGraph.varAbstraction(dsrc, srcm), srcm, srcs);
				allSrcs.add(srcNode);
			}
		}
			
		Set<SVTNode> allTgts = new LinkedHashSet<SVTNode>();
		NodeDefUses tgtNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(tgts);
		List<Variable> defsAtTgt = tgtNdu.getDefinedVars();
		if (defsAtTgt.size() < 1) {
			/** model a CDEdgeVar variable for such CD target in order to create a SVTNode for it */
			Variable tgtVar = makeCDEdgeVar(tgtNdu);
			SVTNode tgtNode = new SVTNode(StaticTransferGraph.varAbstraction(tgtVar, srcm), tgtm, tgts);
			allTgts.add(tgtNode);
		}
		else {
			for (Variable dtgt : defsAtTgt) {
				SVTNode tgtNode = new SVTNode(StaticTransferGraph.varAbstraction(dtgt, srcm), tgtm, tgts);
				allTgts.add(tgtNode);
			}
		}
		
		// now connect each source to each target to form intraCD edges
		assert srcm.equals(tgtm);
		for (SVTNode srcn : allSrcs) {
			for (SVTNode tgtn : allTgts) {
				SVTEdge e = new SVTEdge(srcn, tgtn, VTEType.VTE_CONTROL_INTRA);
				addEdge(e);
				_edges.add(e);
			}
		}
		
		return _edges;
	}
	
	/** create an exhaustive set of control transfer edges from each def (we are still doing <b>flow-insensitive analysis</b>) 
	 * of the used var at the CD edge source to each used var at the control edge target, using a symbolic variable as the place-holder
	 *   for the "variable" field of VTG node ONLY when the target is a call site without any parameters passed into
	 *   
	 *   CAUTION: this exhaustive approach could be wrong!
	 */
	protected Set<SVTEdge> createExhaustiveCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts) {
			Set<SVTEdge> _edges = new LinkedHashSet<SVTEdge>();		
		// if the CD edge involves one or two virtual nodes, "ENTRY" or "EXIT", we would only be able to create symbolic CD for it
		// since there is no variable use/def at at least one vertex
		if ( (srcs instanceof AugmentedUnit) || 
				(tgts instanceof AugmentedUnit)) {
			_edges.addAll(createSymbolicCDEdges(srcm, srcs, tgtm, tgts));
			return _edges;
		}
		
		NodeDefUses tgtNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(tgts);
		// if the CD target is a call site, we just create symbolic CDs to each application callee
		CallSite tgtcs = tgtNdu.getCallSite();
		if (tgtcs != null && tgtcs.hasAppCallees()) {
			int naParams = tgtcs.getNumActualParams();
			InvokeExpr iex = tgtcs.getLoc().getStmt().getInvokeExpr();
			int startArgIdx = 0;
			if (iex instanceof InstanceInvokeExpr /*&& cs.isInstanceCall()*/) {
				startArgIdx = 1;
			}
			if (naParams - startArgIdx < 1) {
				// no parameters passed into
				for (SootMethod ce : tgtcs.getAppCallees()) {
					 // stmt "tgts" here is just a place-holder now; we just want to propagate change impact from srcm to ce
					_edges.addAll(createSymbolicCDEdges(srcm, srcs, ce, tgts));
				}
				return _edges;
			}
		}
		
		NodeDefUses srcNdu = (NodeDefUses) ProgramFlowGraph.inst().getNode(srcs);
		List<Variable> usesAtSrc = srcNdu.getUsedVars();
		
		List<Variable> usesAtTgt = tgtNdu.getUsedVars();
		for (Variable usrc : usesAtSrc) {
			Set<SVTNode> defs4use = StaticTransferGraph.getAllDefs(this.curDefSet, usrc, srcm, srcNdu);
			for (SVTNode dn : defs4use) {
				if ( (usrc.isArrayRef() && dn.getVar().isArrayRef())  || (usrc.isFieldRef() && dn.getVar().isFieldRef()) ) {
					if (!srcm.equals(dn.getMethod())) {
						// we care about intraprocedural defs only to avoid redundant edges - we already have 
						// interprocedural value transfer edges connecting writers to readers of ArrayRefs and FieldRefs 
						continue;
					}
				}
				
				// connect each def of used variable at CD source to each used var at the CD target 
				for (Variable utgt : usesAtTgt) {
						//Variable tgtv = new StdVariable(utgt.getValue());
						SVTNode tgtn = new SVTNode( StaticTransferGraph.varAbstraction(utgt, tgtm) , tgtm, tgts );
						SVTEdge e = null;
						if (srcm.equals(tgtm)) {
							e = new SVTEdge(dn, tgtn, VTEType.VTE_CONTROL_INTRA);
						}
						else {
							e = new SVTEdge(dn, tgtn, VTEType.VTE_CONTROL_INTER);
						}
						addEdge(e);
						_edges.add(e);
				} // for each used var at the CD target
			} // for each def of the used var at the CD source
		} // traverse all used variable at the CD source
		
		return _edges;
	}
	
	protected void createCDGEdge(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts) {
		SVTEdge e = makeSymbolicCDEdge(srcm, srcs, tgtm, tgts);
		addCDGEdge(e);
	}
	
	/** Add edges that are supposed to be merged into Value Transfer Graph 
	 * These edges can be either "symbolic" or "value-transfer" edges 
	 */
	public void addEdge(SVTEdge edge) {
		if (edges.contains(edge)) {
			return;
		}
		SVTNode src = edge.getSource(), tgt = edge.getTarget();
		
		nodes.add(src);
		nodes.add(tgt);
		edges.add(edge);
		
		Set<SVTEdge> outEdges = nodeToEdges.get(src);
		if (null == outEdges) {
			outEdges = new LinkedHashSet<SVTEdge>();
		}
		outEdges.add(edge);
		nodeToEdges.put(src, outEdges);
	}
	
	/** Add edges into the Control Dependence Graph itself 
	 */
	public void addCDGEdge(SVTEdge edge) {
		if (CDEdges.contains(edge)) {
			return;
		}
		SVTNode src = edge.getSource(), tgt = edge.getTarget();
		
		CDNodes.add(src);
		CDNodes.add(tgt);
		CDEdges.add(edge);
		
		Set<SVTEdge> outEdges = nodeToCDGEdges.get(src);
		if (null == outEdges) {
			outEdges = new LinkedHashSet<SVTEdge>();
		}
		outEdges.add(edge);
		nodeToCDGEdges.put(src, outEdges);
		
		Set<SVTEdge> inEdges = nodeToInCDGEdges.get(tgt);
		if (null == inEdges) {
			inEdges = new HashSet<SVTEdge>();
		}
		inEdges.add(edge);
		nodeToInCDGEdges.put(tgt, inEdges);
	}
	
	public Set<SVTNode> getPredsOf(SVTNode _node) {
		Set<SVTNode> rets = new LinkedHashSet<SVTNode>();
		if (nodeToInCDGEdges.get(_node) != null) {
			for (SVTEdge e : nodeToInCDGEdges.get(_node)) {
				rets.add(e.getTarget());
			}
		}
		return rets;
	}
	public Set<SVTNode> getSuccsOf(SVTNode _node) {
		Set<SVTNode> rets = new LinkedHashSet<SVTNode>();
		if (nodeToCDGEdges.get(_node) != null) {
			for (SVTEdge e : nodeToCDGEdges.get(_node)) {
				rets.add(e.getTarget());
			}
		}
		return rets;
	}
	
	protected void addVirtualCDEdges() {
		for (SVTNode n : heads) {
			this.createCDGEdge(sMethod, this.getCFG().ENTRY/*CompleteUnitGraphEx.ENTRY*/, sMethod, n.getStmt());
		}
		// now the CDG has a single head, namely the "ENTRY" node
		entryDependents = new ArrayList<SVTNode>(heads);
		heads.clear();
		Variable entryVar = new StdVariable( IntConstant.v(SymbolicCDSource.SCDS_ENTRY) );
		heads.add( new SVTNode(entryVar, sMethod, this.getCFG().ENTRY/*CompleteUnitGraphEx.ENTRY*/) );
	}
	
	protected void buildHeadsAndTails(ExceptionalUnitGraph cg) { 
		Iterator<Unit> cgIt = cg.iterator();
		while (cgIt.hasNext()) {
			Stmt s = (Stmt) cgIt.next();
			// search s in the current CDNodes
			SVTNode sn = null;
			for (SVTNode n : CDNodes) {
				if (n.getStmt().equals(s)) {
					sn = n;
					break;
				}
			}
			
			boolean bTail = true;
			boolean bHead = true;
			if (null != sn) {
				if (getOutCDGEdges(sn)!=null && getOutCDGEdges(sn).size()>=1) {
					bTail = false;
				}
				if (getInCDGEdges(sn)!=null && getInCDGEdges(sn).size()>=1) {
					bHead = false;
				}
			}
			else {
				Variable srcv = null;
				if (s instanceof AugmentedUnit) {
					/** Virtual nodes: ENTRY/EXIT */
					srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_ENTRY));
				}
				else if (s.fallsThrough()) {
					/** ordinary sequential fall-through */
					srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_FALLTHROUGH));
				}
				else {
					/** Returns */
					if (dua.util.Util.isReturnStmt(s)) {
						srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_RETURN));
					}
					else {
						srcv = new StdVariable(IntConstant.v(SymbolicCDSource.SCDS_OTHER));
					}
				}
				sn = new SVTNode( srcv, sMethod, s);
			}
			
			if (bTail) {
				tails.add(sn);
			}
			if (bHead) {
				heads.add(sn);
			}
		}
	}
	
	public int dumpInternals(boolean listByMethod) {
		if (!listByMethod) {
			System.out.println(this);
			return 0;
		}
		
		/* list nodes by enclosing methods */
		Map<SootMethod, List<SVTNode>> method2nodes = new LinkedHashMap<SootMethod, List<SVTNode>>();
		for (SVTNode vn : CDNodes) {
			List<SVTNode> vns = method2nodes.get(vn.getMethod());
			if (vns == null) {
				vns = new LinkedList<SVTNode>();
				method2nodes.put(vn.getMethod(), vns);
			}
			vns.add(vn);
		}
		for (Map.Entry<SootMethod, List<SVTNode>> en : method2nodes.entrySet()) {
			System.out.println("----------------------------------------- " + en.getKey().getSignature()
					/*en.getKey().getDeclaringClass().getName() +"::"+ en.getKey().getName()*/ + " [" +	en.getValue().size() + 
					" nodes] -----------------------------------------");
			for (SVTNode vn : en.getValue()) {
				System.out.println("\t"+vn);
			}
		}
		
		System.out.println("----------------------------------------- " + " [" +	CDEdges.size() + " total edges] -----------------------------------------");
		for (SVTEdge e : CDEdges) {
			System.out.println("\t"+e);
		}
		
		return 0;
	}
}

/* vim :set ts=4 tw=4 tws=4 */
