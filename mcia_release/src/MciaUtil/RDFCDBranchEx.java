/**
 * File: src/MciaUtil/RDFCDBranchEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 10/21/13		hcai		created; compute RDF and CD branches based on an exceptional CFG;
 *							as opposed to ReqBranchAnalysis in DuaF which is based on a CFG with exceptional units
 *							ignored
 * 10/22/13		hcai		reached first workable version; added getAllUniqueBranches()
 * 10/25/13		hcai		fixed a few issues encountered with xmlsec and jmeter
 * 
*/
package MciaUtil;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import MciaUtil.CompleteUnitGraphEx;

import dua.global.ProgramFlowGraph;
import dua.method.CFG;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.Branch;
import dua.method.CFGDefUses.Branch.BranchComparator;
import fault.StmtMapper;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.toolkits.graph.ExceptionalUnitGraph;

/**
 *	Compute the full set of CD branches, including separately the RDF and non-RDF branch subset, of the entire program under analysis,
 * based on the Exceptional CFG (ExceptionalUnitGraph); This class can be regarded as an "exceptional" version of DuaF's 
 * ReqBranchAnalysis, which ignores all exceptional units (e.g. statements in catch blocks and finally blocks)
 */
public class RDFCDBranchEx {
	/** the map from a method to all branches in it */
	private Map<SootMethod, Set<Branch>> me2BranchSet = null;
	/** the map from a method to its mapping of cfg node to incoming branch set */
	private Map<SootMethod, Map<CFGNode, Set<Branch>>> node2InBranchSet = null; 

	/** aggregate set of branches over the entire program under analysis */
	private List<Branch> allBranches = null;
	
	/** aggregate set of Unique branches over the entire program under analysis
	 *   a branch is unique in this list when there are no any other branches sharing the same set of CD statements control
	 *   dependent on it as its  
	 */
	private List<Branch> allUniqueBranches = null;
	
	/** the map from a method to its mapping of cfg node to RDF branch set */
	private Map<SootMethod, Map<CFGNode, Set<Branch>>> node2RDFBranchSet = null; 
	/** the map from a method to its mapping of cfg node to CD branch set excluding RDF branches */
	private Map<SootMethod, Map<CFGNode, Set<Branch>>> node2NonRDFCDBranchSet = null; 
	
	/** the map from a method to its exceptional cfg */
	private Map<SootMethod, CompleteUnitGraphEx> me2excfg = null;
	/** the map from a method to its postdominator finder */
	private Map<SootMethod, MHGPostDominatorsFinderEx> me2pdomFinder = null;
	
	/** the map from a branch to all statements that are control dependent on it, for the entire program under analysis */
	private Map<Branch, Set<Stmt>> branch2CDStmts = null;
	
	/** get the branch->CDStmts mapping for all branches */
	public Map<Branch, Set<Stmt>> getAllBranchCDStmtsMap() {
		if (null == branch2CDStmts) {
			branch2CDStmts = buildBranchToCDStmtsMap(getAllBranches(), StmtMapper.getWriteGlobalStmtIds());
		}
		
		return branch2CDStmts;
	}
	
	/** a set of accessories */
	public Set<Branch> getRDFBranches(SootMethod m, CFGNode n) { return getRDFBranchSets().get(m).get(n); }
	public Set<Branch> getRDFBranches(CFGNode n) { 
		return getRDFBranchSets().get(ProgramFlowGraph.inst().getContainingMethod(n)).get(n); 
	}
	public Set<Branch> getNonRDFCDBranches(SootMethod m, CFGNode n) { return getNonRDFCDBranchSets().get(m).get(n); }
	public Set<Branch> getNonRDFCDBranches(CFGNode n) { 
		return getNonRDFCDBranchSets().get(ProgramFlowGraph.inst().getContainingMethod(n)).get(n); 
	}
	
	public Map<SootMethod, Map<CFGNode, Set<Branch>>> getRDFBranchSets() {
		createIntraCDBranches();
		return node2RDFBranchSet;
	}
	public Map<SootMethod, Map<CFGNode, Set<Branch>>> getNonRDFCDBranchSets() {
		createIntraCDBranches();
		return node2NonRDFCDBranchSet;
	}
	
	private CompleteUnitGraphEx getCreateExceptionalCFG(SootMethod m) {
		if (me2excfg == null) {
			me2excfg = new LinkedHashMap<SootMethod, CompleteUnitGraphEx>();
		}
		
		CompleteUnitGraphEx excfg = me2excfg.get(m);
		if (null == excfg) {
			excfg = new CompleteUnitGraphEx(m.retrieveActiveBody());
			me2excfg.put(m, excfg);
		}
		return excfg;
	}
	
	private MHGPostDominatorsFinderEx getCreatePDomFinder(SootMethod m) {
		if (me2pdomFinder == null) {
			me2pdomFinder = new LinkedHashMap<SootMethod, MHGPostDominatorsFinderEx>();
		}
		
		MHGPostDominatorsFinderEx pdomFinder = me2pdomFinder.get(m);
		if (null == pdomFinder) {
			ExceptionalUnitGraph cg = getCreateExceptionalCFG(m);
			pdomFinder = new MHGPostDominatorsFinderEx(cg);
			me2pdomFinder.put(m, pdomFinder);
		}
		return pdomFinder;
	}
	
	// use singleton for this analyzer
	private static RDFCDBranchEx instance = null;
	public static RDFCDBranchEx inst() {
		if (null == instance) {
			instance = new RDFCDBranchEx();
		}
		return instance;
	}
	private RDFCDBranchEx() {
	}
	
	/** the following two accessories are offered here just for creating compatibility between DuaF's CFGNode and
	 *  Unit of Diver's exceptional CFG, in order to reuse the "Branch" data structure and facilities for coverage monitoring
	 *  that are built on that data structure  
	 */
	protected CFGNode getCFGNode(CompleteUnitGraphEx cg, Unit u) {
		CFG duacfg = ProgramFlowGraph.inst().getCFG(cg.getBody().getMethod());
		if (u == cg.ENTRY) { return duacfg.ENTRY; }
		if (u == cg.EXIT) { return duacfg.EXIT; }
		
		// for "real" nodes, just get the corresponding CFG node modeled by DuaF
		return duacfg.getNode((Stmt)u);
	}
	protected Unit getExceptionalCFGUnit(CFG cfg, CFGNode n) {
		CompleteUnitGraphEx cg = getCreateExceptionalCFG(cfg.getMethod());
		if (n.isSpecial()) {
			if (n == cfg.ENTRY) { return cg.ENTRY; }
			if (n == cfg.EXIT) { return cg.EXIT; }
		}
		
		// for "real" nodes, just get the corresponding Exceptional CFG node modeled by Diver too
		return n.getStmt();
	}
	
	/** create all intraprocedural CD branches, including separately the set of RDF branches for each method */
	private void createIntraCDBranches() {
		if (node2RDFBranchSet != null || node2NonRDFCDBranchSet != null) {
			// already done before
			return;
		}
		node2RDFBranchSet = new LinkedHashMap<SootMethod, Map<CFGNode, Set<Branch>>>();
		node2NonRDFCDBranchSet = new LinkedHashMap<SootMethod, Map<CFGNode, Set<Branch>>>();
		
		// to compute CD branches, the mapping from method/node to incoming branch needs be ready 
		createAllBranches();
		
		for (SootMethod m:ProgramFlowGraph.inst().getReachableAppMethods()) {
			CFG duacfg = ProgramFlowGraph.inst().getCFG(m);
			
			MHGPostDominatorsFinderEx pDomFinder = getCreatePDomFinder(m);
			CompleteUnitGraphEx cg = getCreateExceptionalCFG(m);
			
			Map<CFGNode, Set<Branch>> node2RDFBrs = node2RDFBranchSet.get(m);
			if (null == node2RDFBrs) {
				node2RDFBrs = new LinkedHashMap<CFGNode, Set<Branch>>();
				node2RDFBranchSet.put(m, node2RDFBrs);
			}
			
			Map<CFGNode, Set<Branch>> node2NonRDFCDBrs = node2NonRDFCDBranchSet.get(m);
			if (null == node2NonRDFCDBrs) {
				node2NonRDFCDBrs = new LinkedHashMap<CFGNode, Set<Branch>>();
				node2NonRDFCDBranchSet.put(m, node2NonRDFCDBrs);
			}
			
			// traverse all nodes of the CFG : DuaF's cfg contains exceptional units too
			for (CFGNode n : duacfg.getNodes()) {
				Set<Branch> inbrs = node2InBranchSet.get(m).get(n);
				if (null == inbrs) {
					// no CD branches can be inferred from current node
					continue;
				}
				
				Unit un = getExceptionalCFGUnit(duacfg, n);
				// traverse all post-dominators of the current cfg node
				for (Object opdom : pDomFinder.getDominators(un)) {
					CFGNode npdom = getCFGNode(cg, (Unit)opdom); //ProgramFlowGraph.inst().getNode((Stmt)opdom);
					
					Set<Branch> RDFBrs = node2RDFBrs.get(npdom);
					if (null == RDFBrs) {
						RDFBrs = new LinkedHashSet<Branch>();
						node2RDFBrs.put(npdom, RDFBrs);
					}
					
					Set<Branch> NonRDFCDBrs = node2NonRDFCDBrs.get(npdom);
					if (null == NonRDFCDBrs) {
						NonRDFCDBrs = new LinkedHashSet<Branch>();
						node2NonRDFCDBrs.put(npdom, NonRDFCDBrs);
					}
					
					for (Branch br : inbrs) {
						if (br.getSrc() == null) {
							// entry branch
							RDFBrs.add(br);
							continue;
						}
						
						// a RDF branch : branch source is not post-dominated by npdom
						Unit uBrsrc = getExceptionalCFGUnit(duacfg, br.getSrc());
						if (!pDomFinder.isDominatedBy(uBrsrc/*br.getSrc().getStmt()*/, (Stmt)opdom)) {
							RDFBrs.add(br);
							continue;
						}
						
						// otherwise, a non-RDF CD branch : there exists at least one successor of n that is not post-dominated by npdom
						for (Unit usucc : cg.getSuccsOf(un)) {
							if (!pDomFinder.isDominatedBy(usucc, (Stmt)opdom)) {
								NonRDFCDBrs.add(br);
								break;
							}
						}
					} // examine each incoming branch of the current cfg node
				} // examine each post-dominator of the current cfg node
			} // for each cfg node
		} // for each method
	} // createIntraCDBranches
	
	/** create all branches for a given method just according to its exceptional CFG : the unit graph */
	private Set<Branch> createBranches(SootMethod m, Map<CFGNode, Set<Branch>> node2inbrs) {
		Set<Branch> brs = new LinkedHashSet<Branch>();
		
		if (m.getActiveBody().getUnits().size() < 1) {
			// no need to do anything further along with an empty method
			System.out.println("empty method skipped : " + m.getSignature());
			return brs;
		}
		
		CompleteUnitGraphEx cg = getCreateExceptionalCFG(m);
		CFG duacfg = ProgramFlowGraph.inst().getCFG(m);
		
		/** A multi-headed CFG may not need a virtual Entry branch at all (this will never happen when ignoring exceptional units, and
		 *  is why DuaF always adds the Entry branch for each CFG), but sometimes it is still necessary even in that type of CFG;
		 *  otherwise, we need one
		 */
		//if (cg.getSuccsOf(cg.getHeads().get(0)).size() <= 1) 
		{
			// the special entry branch
			Branch sbr = duacfg.getEntryBranch();
			brs.add(sbr);
			Set<Branch> entryRDFBranches = new HashSet<Branch>();
			entryRDFBranches.add( sbr );
			node2inbrs.put(duacfg.ENTRY, entryRDFBranches);
		}/*
		else {
			System.out.println("rare case with Entry branch not needed in multiple-headed CFG: " + m.getSignature());
		}*/
		
		Iterator<Unit> cgIter = cg.iterator();
		while (cgIter.hasNext()) {
			Unit u = cgIter.next();
			
			List<Unit> succs = cg.getSuccsOf(u);
			if (succs.size() <= 1) {
				// cann't be a branch source
				continue;
			}
			
			for (Unit succ : succs) {
				// to reuse duaf's branch class, cast unit to its CFGNode structure
				CFGNode n = getCFGNode(cg, u); //ProgramFlowGraph.inst().getNode((Stmt)u);
				CFGNode nsucc = getCFGNode(cg, succ); //ProgramFlowGraph.inst().getNode((Stmt)succ);
				Branch br = new Branch(n, nsucc);
				
				if (nsucc == duacfg.EXIT) {
					System.out.println("rare case with EXIT as a branch target: " + br);
					// for such a branch, no way (there might be, by wrapping another catch block) to monitor it, 
					// and actually no need to do that either
					continue;
				}
				
				ArrayList<Branch> brlist = new ArrayList<Branch>(brs);
				int iloc = brlist.indexOf(br);
				if (-1 == iloc /*!brs.contains(br)*/) {
					brs.add(br);
				}
				else {
					br = brlist.get(iloc);
				}
				
				// create mapping from cfg node to its incoming branches
				Set<Branch> inbrs = node2inbrs.get(nsucc);
				if (null == inbrs) {
					inbrs = new LinkedHashSet<Branch>();
				}
				inbrs.add(br);
				node2inbrs.put(nsucc, inbrs);
			}
		}
		return brs;
	} // createBranches
	
	/** build the entire map of method to branch set for the whole program under analysis */
	private int createAllBranches() {
		if (me2BranchSet != null || node2InBranchSet != null) {
			// already done before
			return 0;
		}
		
		me2BranchSet = new LinkedHashMap<SootMethod, Set<Branch>>();
		node2InBranchSet = new LinkedHashMap<SootMethod, Map<CFGNode, Set<Branch>>>();
		
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
				
				// trivial: omit unreachable methods
				if (!ProgramFlowGraph.inst().getReachableAppMethods().contains(sMethod)) {
					// it is pointless to monitor branches in unreachable methods
					continue;
				}
				
				Map<CFGNode, Set<Branch>> node2inbrs = node2InBranchSet.get(sMethod);
				if (null == node2inbrs) {
					node2inbrs = new LinkedHashMap<CFGNode, Set<Branch>>(); 
				}
				
				me2BranchSet.put(sMethod, createBranches(sMethod, node2inbrs));
				
				// create mapping from method to its node->incomingBranchSet map
				node2InBranchSet.put(sMethod, node2inbrs);
			} // for each method
		} // for each class
		return 0;
	} // createAllBranches
	
	/** collect the set of unique branches for the entire program under analysis */
	public List<Branch> getAllUniqueBranches() {
		if (allUniqueBranches != null) {
			// already computed
			return allUniqueBranches;
		}
		
		List<Branch> brs = getAllBranches();
		
		// clustering all branches according to their target nodes
		Map<CFGNode, Set<Branch>> tgtCluster = new LinkedHashMap<CFGNode, Set<Branch>>();
		for (Branch b : brs) {
			if (!tgtCluster.containsKey(b.getTgt())) {
				tgtCluster.put(b.getTgt(), new LinkedHashSet<Branch>());
			}
			tgtCluster.get(b.getTgt()).add(b);
		}
		
		Map<Branch, Set<Stmt>> br2cdstmts = getAllBranchCDStmtsMap();
		Set<Branch> allBrs = new LinkedHashSet<Branch>();
		int nRemoved = 0;
		for (Map.Entry<CFGNode, Set<Branch>> en : tgtCluster.entrySet()) {
			if (en.getValue().size() == 1) {
				// no repeated branches, immediately add it to the final set
				allBrs.addAll(en.getValue());
				continue;
			}
			assert en.getValue().size() > 1;
			Iterator<Branch> iter = en.getValue().iterator();
			Branch firstb = iter.next();
			Set<Stmt> firstStmtSet = br2cdstmts.get(firstb);
			// the first branch in each cluster should always be added to the final set
			allBrs.add(firstb);
			while (iter.hasNext()) {
				Branch nextb = iter.next();
				Set<Stmt> nextStmtSet = br2cdstmts.get(nextb);
				// the two sets can not be the same if they are different in size in the first place
				if (firstStmtSet.size() != nextStmtSet.size()) {
					allBrs.add(nextb);
					continue;
				}
				nextStmtSet.removeAll(firstStmtSet);
				if (nextStmtSet.isEmpty()) {
					nRemoved ++;
				}
				else {
					allBrs.add(nextb);
				}
			}
		}
		System.out.println(brs.size()-tgtCluster.keySet().size() + " plausible repeated branches, " + nRemoved + " removed.");
		allUniqueBranches = new ArrayList<Branch>(allBrs);

		// sort branches and return
		Collections.sort(allUniqueBranches, new BranchComparator());
		return allUniqueBranches;
	}
	
	/** collect the full set of branches for the entire program under analysis */
	public List<Branch> getAllBranches() {
		// by default, keep all branches including repeated ones in terms of same targets
		return getAllBranches(false);
	}
	public List<Branch> getAllBranches(boolean removeRepeated) {
		if (allBranches != null) {
			// already computed
			return allBranches;
		}
		// instantiate all real (as opposed to virtual ones such as entryBranches) branches
		createAllBranches();
		
		Set<Branch> brs = new LinkedHashSet<Branch>();
		// simply merge branches over all methods, including entry branches and real CD-wise branches
		for (SootMethod m : me2BranchSet.keySet()) {
			brs.addAll(me2BranchSet.get(m));
			
			//brs.add(ProgramFlowGraph.inst().getCFG(m).getEntryBranch());
		}
		
		if (removeRepeated) {
			// for branches sharing targets, we need instrument only any one of them since the monitor will only 
			// be inserted at the target. 
			// NOTE: this might not be safe because two branches sharing target may have different set of CD statements associated with  
			Set<CFGNode> uniqTgts = new LinkedHashSet<CFGNode>();
			Set<Branch> allBrs = new LinkedHashSet<Branch>();
			for (Branch br : brs) {
				if (uniqTgts.contains(br.getTgt())) {
					// avoid repeated ones
					continue;
				}
				uniqTgts.add(br.getTgt());
				allBrs.add(br);
			}
			allBranches = new ArrayList<Branch>(allBrs);
		}
		else {
			allBranches = new ArrayList<Branch>(brs);
		}
		
		// sort branches
		Collections.sort(allBranches, new BranchComparator());
		
		return allBranches;
	} // getAllBranches
	
	/**
	 *   create a mapping from a branch to all statements that are control dependent on it, following the same rule as DuaF's 
	 *   BranchStmtMapper does but using RDFCDBranchEx in Diver instead of ReqBranchAnalysis in DuaF
	 *   
	 *   1) Stmt that are directly control-dependent on the branch, ordered from closer to farther from branch (i.e., by idx in CFG)
	 *   2) If there are no control-dependent stmts for a branch, pick branches on which this branch's tgt is control-dependent and
	 *      select stmts associated to those branches that postdominate the tgt stmt.
	 */
	public Map<Branch, Set<Stmt>> buildBranchToCDStmtsMap(List<Branch> branches, Map<Stmt,Integer> stmtIds) {
		Map<Branch, Set<Stmt>> branchToCDStmts = new LinkedHashMap<Branch, Set<Stmt>>();
		BitSet bsAssignedStmts = new BitSet(stmtIds.size()); // keeps track of which stmts have not been associated
		
		// Build maps branch->stmt by visiting each cfg node
		// Associate each stmt to control-dependencies
		for (CFG cfg : ProgramFlowGraph.inst().getCFGs()) {
			for (CFGNode n : cfg.getNodes()) {
				
				Stmt s = n.getStmt();
				if (s == null) {
					// skip ENTRY and EXIT
					continue; 
				}
				
				// Rule 1: Associate stmt to branches on which stmt is control-dependent
				Set<Branch> rdfBrs = getRDFBranches(cfg.getMethod(), n);
				for (Branch br : rdfBrs) {
					// get/create list of stmts for branch
					Set<Stmt> relStmts = branchToCDStmts.get(br);
					if (relStmts == null) {
						relStmts = new LinkedHashSet<Stmt>();
						branchToCDStmts.put(br, relStmts);
					}
					// add stmt to list associated to branch
					relStmts.add(s);
					bsAssignedStmts.set(stmtIds.get(s));
				}
			}
		}
		
		// Some branches don't get any stmt associated with rule 1; use rule 2 in such cases
		Map<Branch, CFG> entryBranchesToRemove = new LinkedHashMap<Branch, CFG>();
		for (Branch br : branches) {
			Set<Stmt> relStmts = branchToCDStmts.get(br);
			if (relStmts == null) {
				// create new list for branch
				relStmts = new LinkedHashSet<Stmt>();
				branchToCDStmts.put(br, relStmts);
				
				// get control-dependencies and local dominator data for branch's tgt
				CFGNode nTgt = br.getTgt();
				CFG cfg = ProgramFlowGraph.inst().getContainingCFG(nTgt);
				MHGPostDominatorsFinderEx pDomFinder = getCreatePDomFinder(cfg.getMethod());
								
				// Rule 2: For each required branch of tgt, select associated stmts that postdominate the tgt
				Set<Branch> tgtRdfBrs = getRDFBranches(cfg.getMethod(), nTgt);
				for (Branch brRdf : tgtRdfBrs) {
					Set<Stmt> rdfTgtBrRelStmts = branchToCDStmts.get(brRdf);
					for (Stmt relS : rdfTgtBrRelStmts) {
						Unit uTgt = this.getExceptionalCFGUnit(cfg, nTgt);
						if (pDomFinder.isDominatedBy(uTgt/*nTgt.getStmt()*/, relS)) {
							relStmts.add(relS);
							bsAssignedStmts.set(stmtIds.get(relS));
						}
					}
				}
			}
			
			if (relStmts.isEmpty()) {
				/** for some multiple-headed CFG, the entry branch is not needed at all because no statements will be CD on it; 
				 *   unfortunately we have to wait until now, namely when the branch->CD stmt mapping has been computed for them, to know
				 *   that; 
				 *   Once we know that, we can remove them for sure now
				 */
				CFG targetCfg = null;
				for (CFG cfg : ProgramFlowGraph.inst().getCFGs()) {
					if (cfg.getEntryBranch() == br) {
						targetCfg = cfg;
 						break;
					}
				}
				if (null == targetCfg) {
					// problematic is not an entry branch: something fatal
					System.out.println("problematic branch is " + br);
					assert false;
				}
				CompleteUnitGraphEx cg = this.getCreateExceptionalCFG(targetCfg.getMethod());
				if ( cg.getSuccsOf(cg.getHeads().get(0)).size() > 1 ) {
					// expected case, exempt it
					entryBranchesToRemove.put(br, targetCfg);
					continue;
				}
				else {
					// something wrong
					System.out.println("problematic branch is " + br);
					cg.dumpCFG();
				}
			}
			assert !relStmts.isEmpty();
		}
		
		// remove the entry branches on which no any statements are dependent on
		for (Branch br : entryBranchesToRemove.keySet()) {
			branches.remove(br);
			branchToCDStmts.remove(br);
			
			CFG cfg = entryBranchesToRemove.get(br);
			SootMethod m = cfg.getMethod();
			
			if (this.node2InBranchSet.get(m).containsKey(cfg.ENTRY)) {
				this.node2InBranchSet.get(m).get(cfg.ENTRY).remove(br);
				if (this.node2InBranchSet.get(m).get(cfg.ENTRY).isEmpty()) {
					this.node2InBranchSet.get(m).remove(cfg.ENTRY);
				}
			}
			
			this.me2BranchSet.get(m).remove(br);
			this.allBranches.remove(br);
			if (this.allUniqueBranches != null)	this.allUniqueBranches.remove(br);
			if (this.branch2CDStmts != null) this.branch2CDStmts.remove(br);
			
			if (this.node2NonRDFCDBranchSet.get(m).containsKey(cfg.ENTRY)) {
				this.node2NonRDFCDBranchSet.get(m).get(cfg.ENTRY).remove(br);
				/*
				if (this.node2NonRDFCDBranchSet.get(m).get(cfg.ENTRY).isEmpty()) {
					this.node2NonRDFCDBranchSet.get(m).remove(cfg.ENTRY);
				}
				*/
			}
			
			if (this.node2RDFBranchSet.get(m).containsKey(cfg.ENTRY)) {
				this.node2RDFBranchSet.get(m).get(cfg.ENTRY).remove(br);
				/*
				if (this.node2RDFBranchSet.get(m).get(cfg.ENTRY).isEmpty()) {
					this.node2RDFBranchSet.get(m).remove(cfg.ENTRY);
				}
				*/
			}
			
			System.out.println("NOTICE: entry branch from multi-headed CFG has been remove: " + m.getSignature());
		}
		
		// make sure that all stmts have been associated to some branches (i.e. RDF branches directly or indirectly)
		// - DEBUG
		if (bsAssignedStmts.cardinality() != stmtIds.size()) {
			for (Map.Entry<Stmt, Integer> en : stmtIds.entrySet()) {
				if (!bsAssignedStmts.get(en.getValue())) {
					SootMethod m = ProgramFlowGraph.inst().getContainingMethod(en.getKey());
					System.err.println("stmt " + en.getKey() + " in " +  m	+ " has not been assigned any CD branches.");
					CompleteUnitGraphEx cg = this.getCreateExceptionalCFG(m);
					cg.dumpCFG();
				}
			}
		}
		assert bsAssignedStmts.cardinality() == stmtIds.size();
		return branchToCDStmts;
	}
	
	/** now that the the dominance analyses have all done, all assistant virtual nodes (ENTRY/EXIT) should be removed */
	public void removeAssistantNodes() {
		for (SootMethod m:ProgramFlowGraph.inst().getReachableAppMethods()) {
			getCreateExceptionalCFG(m).removeVirtualNodes();
		}
	}
} // definition of RDFCDBranchEx

/* vim :set ts=4 tw=4 tws=4 */
