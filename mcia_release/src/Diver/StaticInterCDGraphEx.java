/**
 * File: src/Diver/StaticInterCDGraphEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created; model an interprocedural exceptional control dependence graph
 * 08/15/13		hcai		first completed computing static interprocedural exceptional CDs
 * 08/18/13		hcai		speeded up the recursive interprocedural CD computation using "dynamic programming"
 * 09/01/13		hcai		added interprocedural exceptional CDs due to uncaught exceptions
 *  
*/
package Diver;

import java.util.ArrayList;
import java.util.HashMap;
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
import dua.method.CFGDefUses.Variable;
import dua.method.CallSite;

import soot.*;
import soot.jimple.*;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.exceptions.UnitThrowAnalysis;

import MciaUtil.*;
import MciaUtil.CompleteUnitGraphEx.AugmentedUnit;
import MciaUtil.VTEdge.VTEType;

/**
 * The static Interprocedural Exceptional Control Dependence Graph that concentrates on computing interprocedural CDs
 * based on the intraprocedural CDs that have already been prepared by per-method invocation of ControlDependenceEx
 */
public class StaticInterCDGraphEx extends InterCDGraphEx<SVTNode, SVTEdge> {
	/** A map from a method to all inteprocedural CD targets starting inside it, created for saving recursive computation cost */
	private final Map<SootMethod, Set<SVTNode>> mInterCDCache = new LinkedHashMap<SootMethod, Set<SVTNode>>();
	
	/** choose if using the cache above to speed up interprocedural CD propagation, namely trade memory for speed */
	private boolean memoryForSpeed = false;
	
	public StaticInterCDGraphEx (boolean debugOut) {
		super(debugOut);
	}
	public StaticInterCDGraphEx () {
		super();
	}
	public void turnMemoryForSpeed(boolean b) {
		memoryForSpeed = b;
	}
	@Override
	public Set<SVTNode> getPredsOf(SVTNode _node) {
		Set<SVTNode> rets = new LinkedHashSet<SVTNode>();
		if (nodeToInCDGEdges.get(_node) != null) {
			for (SVTEdge e : nodeToInCDGEdges.get(_node)) {
				rets.add(e.getTarget());
			}
		}
		return rets;
	}
	@Override
	public Set<SVTNode> getSuccsOf(SVTNode _node) {
		Set<SVTNode> rets = new LinkedHashSet<SVTNode>();
		if (nodeToCDGEdges.get(_node) != null) {
			for (SVTEdge e : nodeToCDGEdges.get(_node)) {
				rets.add(e.getTarget());
			}
		}
		return rets;
	}
	@Override
	protected Set<SVTEdge> createSymbolicCDEdges(SootMethod srcm, Stmt srcs,	SootMethod tgtm, Stmt tgts) {
		Set<SVTEdge> _edges = new LinkedHashSet<SVTEdge>();
		
		SVTEdge e = StaticCDGraphEx.makeSymbolicCDEdge(srcm, srcs, tgtm, tgts);
		addEdge(e);
		_edges.add(e);
		
		return _edges;
	}
	@Override
	protected Set<SVTEdge> createFullCDEdges(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts) {
		Set<SVTEdge> _edges = new LinkedHashSet<SVTEdge>();
		
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
			Variable srcVar = StaticCDGraphEx.makeCDEdgeVar(srcNdu);
			SVTNode srcNode = new SVTNode(StaticTransferGraph.varAbstraction(srcVar, srcm), srcm, srcs);
			allSrcs.add(srcNode);

			/** note that we need create edges from each of the defs of each use at srcs to the monolithic CDEdgeVar, which
			 * however should have been already created when incorporating the IntraCDs to VTG before we are focusing on
			 * the interprocedural CDs here 
			 */
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
			Variable tgtVar = StaticCDGraphEx.makeCDEdgeVar(tgtNdu);
			SVTNode tgtNode = new SVTNode(StaticTransferGraph.varAbstraction(tgtVar, srcm), tgtm, tgts);
			allTgts.add(tgtNode);
		}
		else {
			for (Variable dtgt : defsAtTgt) {
				SVTNode tgtNode = new SVTNode(StaticTransferGraph.varAbstraction(dtgt, srcm), tgtm, tgts);
				allTgts.add(tgtNode);
			}
		}
		
		// now connect each source to each target to form CD edges
		for (SVTNode srcn : allSrcs) {
			for (SVTNode tgtn : allTgts) {
				SVTEdge e = new SVTEdge(srcn, tgtn, 
						srcm.equals(tgtm)?VTEType.VTE_CONTROL_INTRA:VTEType.VTE_CONTROL_INTER);
				addEdge(e);
				_edges.add(e);
			}
		}
		
		return _edges;
	}
	@Override
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
	@Override
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
	@Override
	protected void createCDGEdge(SootMethod srcm, Stmt srcs, SootMethod tgtm, Stmt tgts) {
		SVTEdge e = StaticCDGraphEx.makeSymbolicCDEdge(srcm, srcs, tgtm, tgts);
		addCDGEdge(e);
	}
	@Override
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
	@Override
	public int addMultiCSInterCDs(SVTNode src) {
		if (src.getStmt() instanceof AugmentedUnit) {
			// ENTRY/EXIT are virtual nodes, they won't be likely to have callees
			return 0;
		}
		CFGNode nsrc = ProgramFlowGraph.inst().getNode(src.getStmt());
		CallSite cssrc = nsrc.getCallSite();
		if ( cssrc == null || !cssrc.hasAppCallees() || !(cssrc.getAppCallees().size()>1 || cssrc.hasLibCallees()) ) {
			// not a multiple-target call site.
			/** note that if the call site has both application and library callees, it is still a multi-target CS */
			return 0;
		}
		
		for (SootMethod callee : cssrc.getAppCallees()) {
			ControlDependenceEx<SVTNode, SVTEdge> cecdex = method2cdg.get(callee);
			assert cecdex != null;
			List<SVTNode> entryDependents = cecdex.getEntryDependents();
			assert entryDependents.size()>=1;
			for (SVTNode sn : entryDependents) {
				if (sn.getStmt() instanceof AugmentedUnit) {
					continue;
				}
				
				// direct control dependencies
				if (symbolicCD) {
					this.createSymbolicCDEdges(src.getMethod(), src.getStmt(), sn.getMethod(), sn.getStmt());
				}
				else {
					this.createFullCDEdges(src.getMethod(), src.getStmt(), sn.getMethod(), sn.getStmt());
				}
				if (holisticInterCDG) {
					this.createCDGEdge(src.getMethod(), src.getStmt(), sn.getMethod(), sn.getStmt());
				}
				
				CallSite cs = ProgramFlowGraph.inst().getNode(sn.getStmt()).getCallSite();
				if (cs!=null && cs.hasAppCallees() && cs.getAppCallees().size()==1 && !cs.hasLibCallees()) {
					// continue propagating transitively
					transititveInterCDPropagation(src, cs.getAppCallees().get(0), new LinkedHashSet<SootMethod>());
				}
			}
		}
		
		return 0;
	}
	@Override
	public int addInterCDs(SVTNode src, SVTNode tgt) {
		// (src,tgt) is given as an Intraprocedural CD edge
		if (tgt.getStmt() instanceof AugmentedUnit) {
			// ENTRY/EXIT are virtual nodes, they won't be likely to have callees
			return 0;
		}
		
		// direct control dependencies
		if (symbolicCD) {
			this.createSymbolicCDEdges(src.getMethod(), src.getStmt(), tgt.getMethod(), tgt.getStmt());
		}
		else {
			this.createFullCDEdges(src.getMethod(), src.getStmt(), tgt.getMethod(), tgt.getStmt());
		}
		if (holisticInterCDG) {
			this.createCDGEdge(src.getMethod(), src.getStmt(), tgt.getMethod(), tgt.getStmt());
		}
		
		CFGNode ntgt = ProgramFlowGraph.inst().getNode(tgt.getStmt());
		CallSite cstgt = ntgt.getCallSite();
			
		if (cstgt != null && cstgt.hasAppCallees() && cstgt.getAppCallees().size()==1 && !cstgt.hasLibCallees() ) {
			// we care about application callees only and handle multi-target call site separately
			transititveInterCDPropagation(src, cstgt.getAppCallees().get(0), new LinkedHashSet<SootMethod>());
		}
				
		return 0;
	}
	private void transititveInterCDPropagation(SVTNode src, SootMethod m, Set<SootMethod> visited) {
		if (m.getActiveBody().getUnits().size() > 2000) {
			System.err.println(new Exception().getStackTrace()[0].getMethodName() + ": " + 
					m.getSignature() + " skipped because of its oversize.");
			return;
		}
		if (!visited.add(m)) {
			// already visited
			return;
		}
		
		if (memoryForSpeed) {
			if (!mInterCDCache.containsKey(m)) {
				mInterCDCache.put(m, new LinkedHashSet<SVTNode>());
			}
		}
		
		ControlDependenceEx<SVTNode, SVTEdge> scdex = method2cdg.get(m);
		assert scdex != null;
		List<SVTNode> entryDependents = scdex.getEntryDependents();
		assert entryDependents.size()>=1;
		for (SVTNode sn : entryDependents) {
			if (sn.getStmt() instanceof AugmentedUnit) {
				continue;
			}
			
			// direct control dependencies
			if (symbolicCD) {
				this.createSymbolicCDEdges(src.getMethod(), src.getStmt(), sn.getMethod(), sn.getStmt());
			}
			else {
				this.createFullCDEdges(src.getMethod(), src.getStmt(), sn.getMethod(), sn.getStmt());
			}
			if (holisticInterCDG) {
				this.createCDGEdge(src.getMethod(), src.getStmt(), sn.getMethod(), sn.getStmt());
			}
			
			if (memoryForSpeed) {
				mInterCDCache.get(m).add(sn);
			}
			
			CallSite cs = ProgramFlowGraph.inst().getNode(sn.getStmt()).getCallSite();
			if (cs!=null && cs.hasAppCallees() && cs.getAppCallees().size()==1 && !cs.hasLibCallees()) {
				// continue propagating transitively, contingent on the availability of required targets in the cache
				if (memoryForSpeed) {
					SootMethod curm = cs.getAppCallees().get(0);
					Set<SVTNode> targets = mInterCDCache.get(curm);
					if (targets==null) {
						transititveInterCDPropagation(src, curm, visited);
						// now targets for curm must have been got ready
						assert mInterCDCache.get(curm)!=null;
						mInterCDCache.get(m).addAll(mInterCDCache.get(curm));
					}
					else {
						// targets already computed before, just connecting to each of them
						for (SVTNode _sn : targets) {
							if (symbolicCD) {
								this.createSymbolicCDEdges(src.getMethod(), src.getStmt(), _sn.getMethod(), _sn.getStmt());
							}
							else {
								this.createFullCDEdges(src.getMethod(), src.getStmt(), _sn.getMethod(), _sn.getStmt());
							}
							if (holisticInterCDG) {
								this.createCDGEdge(src.getMethod(), src.getStmt(), _sn.getMethod(), _sn.getStmt());
							}
						}
						mInterCDCache.get(m).addAll(targets);
					}
				}
				else {
					transititveInterCDPropagation(src, cs.getAppCallees().get(0), visited);
				}
			}
		} // for each ENTRY dependent
	}
	
	/** find, backwardly in the call graph, first reached calling method of m, transitively, that may catch any throwable in the given set ts */
	protected CallSite findAnyCatchabe(ThrowableSet ts, SootMethod m, Set<SootMethod> visited) {
		if (!visited.add(m)) {
			// avoid dead-loop
			return null;
		}
		List<CallSite> callers = ProgramFlowGraph.inst().getCFG(m).getCallerSites();
		for (CallSite cs : callers) {
			for (SootMethod crm : cs.getAllCallees()) {
				for (Iterator<Trap> trapIt = crm.getActiveBody().getTraps().iterator(); trapIt.hasNext(); ) {
				    Trap trap = trapIt.next();
				    RefType catcher = trap.getException().getType();
				    
				    ThrowableSet.Pair catchableAs = ts.whichCatchableAs(catcher);
					
					if (catchableAs.getCaught() != ThrowableSet.Manager.v().EMPTY) {
						return cs;
					}
				}
			}
		}
		// not found catchable block in the this level, go backward further 
		for (CallSite cs : callers) {
			SootMethod crm = cs.getLoc().getMethod();
			CallSite tcs = findAnyCatchabe(ts, crm, visited);
			if (tcs != null) {
				return tcs;
			}
		}
		return null;
	}
	
	/** find, forwardly in the call graph, first reached called method of m, transitively, that may throw the given exception by excls */
	protected boolean findAnyThrower(SootClass excls, SootMethod m,  Set<SootMethod> visited) {
		if (!visited.add(m)) {
			// avoid dead-loop
			return false;
		}
		
		if (m.throwsException(excls)) {
			// no more search needed
			return true;
		}
		
		List<CallSite> cses = ProgramFlowGraph.inst().getCFG(m).getCallSites();
		for (CallSite dcs : cses) {
			// with library callees, we won't check deeply in a transitive forward search, we just check the callee itself
			if (dcs.hasLibCallees()) {
				for (SootMethod ce : dcs.getLibCallees()) {
					if (ce.throwsException(excls)) {
						// already found one, that is enough
						return true;
					}
				}
			}
			if (!dcs.hasAppCallees()) {
				// done with this call site
				continue;
			}
			for (SootMethod ce : dcs.getAppCallees()) {
				// for application callees, yes we check forwardly via a transitive search
				if (findAnyThrower(excls, ce, visited)) {
					// got it, no further probing needed
					return true;
				}
			}
		}
		return false;
	}
	
	/** simple algorithm to add exceptional interprocedural CDs due to uncaught exceptions:
	 * 		do a throw analysis for each unit of a method, and connect it back to each of all its caller site if the 
	 * 		throwable cannot be caught within the method (namely there is no any compatible catcher found in the method 
	 */
	public int computeExceptionalInterCDs(SootMethod m, boolean ignoreRuntimeException) {
		Body body = m.getActiveBody();
		PatchingChain<Unit> pchain = body.getUnits();
		Map<Unit, ThrowableSet> unitToCaughtThrowables = new HashMap<Unit, ThrowableSet>(pchain.size());
		
		// always use the default throw analysis, which can be set by corresponding switch in Soot.Options
		//ThrowAnalysis throwAnalysis = Scene.v().getDefaultThrowAnalysis();
		ThrowAnalysis throwAnalysis = UnitThrowAnalysis.v();
		
		// the list of Exceptions this method explicitly declares to possibly throw
		List<SootClass> declaredExceptionClasses = m.getExceptions();
		final RefType runtimeException = Scene.v().getRefType("java.lang.RuntimeException");
		
		// Record the caught exceptions.
		for (Iterator<Trap> trapIt = body.getTraps().iterator(); trapIt.hasNext(); ) {
		    Trap trap = trapIt.next();
		    RefType catcher = trap.getException().getType();
		    for (Iterator<Unit> unitIt = pchain.iterator(trap.getBeginUnit(), pchain.getPredOf(trap.getEndUnit())); unitIt.hasNext(); ) {
		    	Unit unit = unitIt.next();
		    	ThrowableSet thrownSet = unitToCaughtThrowables.get(unit);
				if (thrownSet == null) {
					thrownSet = throwAnalysis.mightThrow(unit);
				}
				
				for (SootClass excls : declaredExceptionClasses) {
					thrownSet.add(excls.getType());
				}
				
				ThrowableSet.Pair catchableAs = thrownSet.whichCatchableAs(catcher);
				
				if (catchableAs.getCaught() != ThrowableSet.Manager.v().EMPTY) {
					unitToCaughtThrowables.put(unit, catchableAs.getCaught());
				} else {
				    // nothing caught by the catcher
				    assert thrownSet == catchableAs.getUncaught();
				    
				    if (ignoreRuntimeException) {
						catchableAs = thrownSet.whichCatchableAs(runtimeException);
						if (catchableAs.getCaught() != ThrowableSet.Manager.v().EMPTY) {
							unitToCaughtThrowables.put(unit, catchableAs.getCaught());
						} else {
						    // no any runtime exception would be thrown actually
						    assert thrownSet == catchableAs.getUncaught();
						}
					}
				}
		    }
		}
		
		List<Stmt> candidateSrcs = new ArrayList<Stmt>();
		// check all units that might throw exceptions that will not be caught by any trap in this method 
		for (Iterator<Unit> iter = pchain.iterator(); iter.hasNext();) {
			Unit u = iter.next();
			if (u instanceof AugmentedUnit) {
				continue;
			}
			Stmt s = (Stmt) u; 
			CFGNode node = ProgramFlowGraph.inst().getNode(s);
			if (node.isSpecial()) {
				continue;
			}
			
			ThrowableSet thrownSet = throwAnalysis.mightThrow(u);
			//ThrowableSet thrownSet = ThrowableSet.Manager.v().EMPTY;
			for (SootClass excls : declaredExceptionClasses) {
				thrownSet.add(excls.getType());
			}
			
			ThrowableSet nonErr = thrownSet.whichCatchableAs(Scene.v().getRefType("java.lang.Error")).getUncaught();
			if ( nonErr	== ThrowableSet.Manager.v().EMPTY) {
				// skip if this unit won't throw non-Error exception : we care about only RunTimeException 
				// (if the ignoringRunTimeException is not set) and declared exception; the Error type exceptions usually are not caught by 
				// user code because there is no way to handle beside ignoring those exceptions
				continue;
			}
			if (unitToCaughtThrowables.containsKey(u)) {
				// skip if this unit might be caught by some trap in this method
				continue;
			}
			
			if (ignoreRuntimeException) {
				ThrowableSet.Pair catchableAs = thrownSet.whichCatchableAs(runtimeException);
				ThrowableSet cset = catchableAs.getUncaught();
				if (cset == ThrowableSet.Manager.v().EMPTY) {
					// skip if this unit won't throw any exception rather than RuntimeException and we want to ignore RuntimeExceptions
					continue;
				}
				
				if (declaredExceptionClasses.isEmpty()) {
					// if we ignore Runtime Exception, then we only care about the declared exceptions
					continue;
				}
				
				if (!(u instanceof ThrowStmt)) {
					CallSite cs = node.getCallSite();
					if (null == cs) {
						// neither a throw statement, nor a call site, we ignore
						continue;
					}
					
					boolean calleeMayThrow = false;
					for (SootClass excls : declaredExceptionClasses) {
						// No! we actually do not to check that transitively even for application callees
						for (SootMethod callee : cs.getAllCallees()) {
							if (callee.throwsException(excls)) {
								// at least one callee may throw one of the declared exceptions
								calleeMayThrow = true;
								break;
							}
						}
						/*
						if (cs.hasLibCallees()) {
							for (SootMethod callee : cs.getLibCallees()) {
								// with library callees, we won't check deeply in a transitive forward search, we just check the callee itself
								if (callee.throwsException(excls)) {
									// at least one callee may throw one of the declared exceptions
									calleeMayThrow = true;
									break;
								}
							}
						}
						if (calleeMayThrow) {
							break;
						}
						
						if (!cs.hasAppCallees()) {
							// no app callees for further examining the current exception excls
							continue;
						}
						for (SootMethod callee : cs.getAppCallees()) {
							// for application callees, yes we check forwardly via a transitive search
							if (findAnyThrower(excls, callee, new HashSet<SootMethod>())) {
								calleeMayThrow = true;
								break;
							}
						}
						if (calleeMayThrow) {
							break;
						}
						*/
					}
					if (!calleeMayThrow) {
						// none of callees may throw any of the declared exceptions
						continue;
					}
				}
				else {
					// now, it is sure that u explicitly throws some exception
					ThrowStmt ts = (ThrowStmt)s;
					ThrowableSet explicitSet = throwAnalysis.mightThrowExplicitly(ts);
					ThrowableSet implicitSet = throwAnalysis.mightThrowImplicitly(ts);
					if (explicitSet==ThrowableSet.Manager.v().EMPTY && implicitSet==ThrowableSet.Manager.v().EMPTY) {
						// since we only care about declared exceptions, skip this unit if does not throw any of those
						continue;
					}
					boolean mayDirectThrow = false;
					for (SootClass excls : declaredExceptionClasses) {
						if (explicitSet.catchableAs(excls.getType()) || implicitSet.catchableAs(excls.getType())) {
							// this throw statement does throw one of the declared exceptions
							mayDirectThrow = true;
						}
					}
					if (!mayDirectThrow) {
						// this throw statement does not throw any exceptions in the declared list
						if ( explicitSet.whichCatchableAs(runtimeException).getUncaught() == ThrowableSet.Manager.v().EMPTY ) {
							// this throw statement just throws a run-time exception, we surely ignore it here with the "ignoreRTECD" enabled already
							continue;
						}
						System.out.println("NOTICE: method [" + m.getSignature() + "] has a throws statement " + ts + 
								" that throws an undeclared exception that is NOT a run-time exception - " + ts.getOp().getType().toString());
					}
				}
			}
			
			// Now, this unit will throw uncaught exceptions that we won't ignore
			// System.out.println("to throw uncaught exceptions: " + s);
			candidateSrcs.add(s);
		}
		
		if (candidateSrcs.isEmpty()) {
			// none of units should be considered
			return 0;
		}
		
		int cnt = 0;
		List<CallSite> callers = ProgramFlowGraph.inst().getCFG(m).getCallerSites();
		for (Stmt src : candidateSrcs) {
			for (CallSite callersite : callers) {
				if (!callersite.hasAppCallees() || !callersite.getAppCallees().contains(m)) {
					continue;
				}
				
				SootMethod tgtm = callersite.getLoc().getMethod();
				Stmt tgt = callersite.getLoc().getStmt();
				if (symbolicCD) {
					this.createSymbolicCDEdges(m, src, tgtm, tgt);
				}
				else {
					this.createFullCDEdges(m, src, tgtm, tgt);
				}
				if (holisticInterCDG) {
					this.createCDGEdge(m, src, tgtm, tgt);
				}
				cnt ++;
			}
		}
		return cnt;
	}
}

/* vim :set ts=4 tw=4 tws=4 */
