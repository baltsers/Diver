/**
 * File: src/McaiUtil/CompleteUnitGraphEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/10/13		hcai		created; extending ExceptionalUnitGraph for adding virtual nodes and edges
 * 08/20/13		hcai		added handling of tail-less cfg as a result of the presence of infinite loop
 *							in there: treated the jumping back GotoStmts as tails
 * 10/22/13		hcai		made the two virtual nodes instance members instead of static class variables 
 *							to avoid potential confusions of using globally indistinct objects of them 
 *							for all such exceptional CFGs;
 *  
*/
package MciaUtil;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import soot.Body;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.UnitBox;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.jimple.internal.JEnterMonitorStmt;
import soot.jimple.internal.JExitMonitorStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.StmtBox;
import soot.options.Options;
import soot.toolkits.exceptions.PedanticThrowAnalysis;
import soot.toolkits.exceptions.UnitThrowAnalysis;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.DominatorNode;
import soot.toolkits.graph.DominatorTree;
import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGPostDominatorsFinder;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.DominatorTreeAdapter;
import soot.toolkits.graph.SimpleDominatorsFinder;
import soot.toolkits.graph.InverseGraph;
import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.UnitGraph;
/** the following are not available in Soot 2.3.0 we are using now*/
/*
import soot.toolkits.graph.pdg.HashMutablePDG;
import soot.toolkits.graph.pdg.PDGNode;
import soot.toolkits.graph.pdg.PDGRegion;
import soot.toolkits.graph.pdg.Region;
*/
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.jimple.toolkits.annotation.logic.LoopFinder;
import soot.toolkits.graph.LoopNestTree;	
/**
 * An extension of CompleteUnitGraph that is added extra nodes and edges to overcome difficulties in constructing
 * (post)domination relations that are used to construct CDG, esp. for a control flow graph having multiple exits (or,
 * even multiple heads)
 * 
 * Also, the extension is directly made from  CompleteUnitGraph because we want to use, by default, the policy of 
 * omitting the implicit exceptional edges from trapped units to exceptional handlers that have no side effects -
 * CompleteUnitGraph, however, adopts the most strict and conservative exceptional analysis by both using "false"
 * of this omitting policy and, PedanticThrowAnalysis, which assumes that every unit can throw exceptions thus is too
 * conservative. For now, we use "UnitThrowAnalysis" as the default, which is most lax throw analysis known.
 */
public class CompleteUnitGraphEx extends ExceptionalUnitGraph /*CompleteUnitGraph*/ {
	public static class AugmentedUnit extends JNopStmt {
		private static final long serialVersionUID = 4133615679673355646L;
		private String name;
		public AugmentedUnit(String name) { this.name = name; }
		
		private SootMethod m;
		public void setMethod (SootMethod _m) { this.m = _m; }
		//@Override public String toString() { return name + "[" + m.getNumberedSubSignature()+"]"; }
		@Override public String toString() { return name + "[" + m.getSignature()+"]"; }
		// @Override public String toString() { return name + "[" + m.getNumber()+"]"; }
	}
	
	/** for identifying the two special nodes */
	public static boolean isEntry(Stmt s) { return s instanceof AugmentedUnit && s.toString().startsWith("ENTRY");}
	public static boolean isExit(Stmt s) { return s instanceof AugmentedUnit && s.toString().startsWith("EXIT");}
	
	/** the two virtual Nodes */
	public final AugmentedUnit ENTRY = new AugmentedUnit("ENTRY");
	public final AugmentedUnit EXIT = new AugmentedUnit("EXIT");
	
	List<Unit> heads = new ArrayList<Unit>(1);
	List<Unit> tails = new ArrayList<Unit>(1);
	
	// keep what we added for temporary uses, so that it is handy to recover the original unit graph
	List<Unit> unitsToRemove = new ArrayList<Unit>(2);
	
	public CompleteUnitGraphEx(Body b) {
		//super(b);
		/** PedanticThrowAnalysis can be too conservative */
		//super(b, PedanticThrowAnalysis.v(), true);
		/** the Default ThrowAnalysis is also the Pedantic one .... */
		/*
		if (Options.v().throw_analysis() == Options.throw_analysis_pedantic) {
			System.out.println("Yes, the default Throw Analysis is Pedantic one!");
		}*/
		super(b, Scene.v().getDefaultThrowAnalysis(), true);
		//super(b, UnitThrowAnalysis.v(), true);
		
		//addVirtualStart();
		
		ENTRY.setMethod(b.getMethod());
		EXIT.setMethod(b.getMethod());
		
		addTwoNodes();
	}
	
	/**
	 * add two extra nodes, one "Start" connecting to each of the heads and one "Stop" joining all the tails, of the
	 * underlying control flow graph
	 */
	protected void addTwoNodes() {
		// add the ENTRY node
		//JEnterMonitorStmt entryStmt = (new JEnterMonitorStmt(Jimple.v().newVariableBox(null).getValue()));
		AugmentedUnit entryStmt = ENTRY; //new AugmentedUnit("ENTRY");
		List<Unit> predsForHeads = new ArrayList<Unit>(1);
		List<Unit> succsOfEntry = new ArrayList<Unit>(1);
		List<Unit> emptySet = new ArrayList<Unit>();
		
		predsForHeads.add(entryStmt);
		for (Unit head : super.getHeads()) {
			unitToUnexceptionalPreds.put(head, predsForHeads);
			succsOfEntry.add(head);
		}
		unitToUnexceptionalSuccs.put(entryStmt, succsOfEntry);
		unitToUnexceptionalPreds.put(entryStmt, emptySet);
		// now the Entry node becomes the sole head of this ACFG
		heads.add(entryStmt);
		
		// add the EXIT node
		//JExitMonitorStmt exitStmt = (new JExitMonitorStmt(Jimple.v().newVariableBox(null).getValue()));
		AugmentedUnit exitStmt = EXIT; //new AugmentedUnit("EXIT");
		List<Unit> predsOfExit = new ArrayList<Unit>(1);
		List<Unit> succsForTails = new ArrayList<Unit>(1);
		
		succsForTails.add(exitStmt);
		/** some CFG may have no exit (those having an infinite loop, for example, often seen in the main loop of service daemon),
		 * then the tail set would be empty. As a result, the virtual EXIT would become an orphan node. 
		 * What is more serious, the PDT built upon such CFG later on would have no head, causing failure in the construction of
		 * CDG (at least, the getInverseFullPath() routine would never terminate because of the lack of head/root of the PDT).
		 * 
		 * To overcome such an issue, we detect the infinite loop in the first place, and then treat the "GotoStmt" statements whose
		 * target is the first unit of the infinite loop ALL as tails, and then connect these tails to EXIT
		 */
		List<Unit> tailList = super.getTails();
		if (tailList.isEmpty()) {
			tailList = findTails();
			assert (!tailList.isEmpty());
		}
		for (Unit tail : tailList) {
		//for (Unit tail : super.getTails()) {
			unitToUnexceptionalSuccs.put(tail, succsForTails);
			predsOfExit.add(tail);
		}
		unitToUnexceptionalPreds.put(exitStmt, predsOfExit);
		unitToUnexceptionalSuccs.put(exitStmt, emptySet);
		// now the Exit node becomes the sole tail of this ACFG
		tails.add(exitStmt);
		
		/*
		unitChain.addFirst(entryStmt);
		unitChain.addLast(exitStmt);
		*/
		Unit insPnt = utils.getFirstNonIdUnit(unitChain);
		if (null != insPnt) {
			unitChain.insertBefore(entryStmt, insPnt);
		}
		else {
			unitChain.addLast(entryStmt);
		}
		unitChain.addLast(exitStmt);
		
		unitsToRemove.add(entryStmt);
		unitsToRemove.add(exitStmt);
		
		// keep the unmodifiability of internal structures
		makeMappedListsUnmodifiable(unitToUnexceptionalSuccs);
		makeMappedListsUnmodifiable(unitToUnexceptionalPreds);
		if (body.getTraps().size() != 0) {
		    unitToSuccs = combineMapValues(unitToUnexceptionalSuccs, 
					   unitToExceptionalSuccs);
		    unitToPreds = combineMapValues(unitToUnexceptionalPreds, 
					   unitToExceptionalPreds);
		}
	}
	
	/** we added the virtual nodes (and related edges) just for the sake of CDG construction;
	 * we did not intend to instrument anything, so now after CDG got constructed, we should
	 * remove the virtual nodes from the unit chain
	 */
	public void removeVirtualNodes() {
		// recover the original UnitGraph underneath: we must do this because UnitGraph::unitChain is the reference to the
		// chain of the Body: we should not hurt the original body by any means
		unitChain.removeAll(unitsToRemove);
		
		/** for edges we added before, namely those connecting the virtual nodes, we don't need recover them
		 * because they did not belong to the UnitGraph but only to the ExceptionalUnitGraph;
		 * Thus those edges do not affect the underlying control flow graph structure;
		 * Same to the heads and tails. 
		 * So, the following recoveries are all optional!
		 */
		// recover the heads and tails of the original CFG
		heads.clear();
		heads.addAll(super.getHeads());
		tails.clear();
		tails.addAll(super.getTails());
		
		// recover the edges of the original UnitGraph
		List<Unit> emptySet = new ArrayList<Unit>();
		for (Unit head : super.getHeads()) {
			unitToUnexceptionalPreds.put(head, emptySet);
		}
		for (Unit tail : super.getTails()) {
			unitToUnexceptionalSuccs.put(tail, emptySet);
		}
		for (Unit u : unitsToRemove) {
			unitToUnexceptionalPreds.remove(u);
			unitToUnexceptionalSuccs.remove(u);
		}
		
		// keep the unmodifiability of internal structures
		makeMappedListsUnmodifiable(unitToUnexceptionalSuccs);
		makeMappedListsUnmodifiable(unitToUnexceptionalPreds);
		if (body.getTraps().size() != 0) {
		    unitToSuccs = combineMapValues(unitToUnexceptionalSuccs, 
					   unitToExceptionalSuccs);
		    unitToPreds = combineMapValues(unitToUnexceptionalPreds, 
					   unitToExceptionalPreds);
		}
	}
	
	/**
	 * added one extra node and two extra edges for CDG construction:
	 * namely, "Start"->Entry labeled "T", and "Start"->Exit labeled "F" 
	 */
	protected void addVirtualStart() {
		/*
		List<UnitBox> headUnits = new ArrayList<UnitBox>();
		for (Unit head : super.getHeads()) {
			headUnits.addAll(head.getUnitBoxes());
		}
		*/
		assert super.getHeads().size()>=1;
		// add the Start node
		/*
		IfStmt startStmt = Jimple.v().newIfStmt(Jimple.v().newCmpgExpr(IntConstant.v(1), IntConstant.v(0)), 
				new StmtBox((Stmt) super.getHeads().get(0)));
		*/
		AugmentedUnit startStmt = new AugmentedUnit("Start");
		List<Unit> predsForHeads = new ArrayList<Unit>(1);
		List<Unit> succsOfStart = new ArrayList<Unit>();
		List<Unit> emptySet = new ArrayList<Unit>();

		// add the edges from Start to heads, with "T", and tails, with "F"
		predsForHeads.add(startStmt);
		for (Unit head : super.getHeads()) {
			// each head now has the Start as the sole predecessor
			unitToUnexceptionalPreds.put(head, predsForHeads);
			// create an edge from the Start to each head
			succsOfStart.add(head);
		}
		
		/** some CFG may have no exit (those having an infinite loop, for example, often seen in the main loop of service daemon),
		 * then the tail set would be empty. As a result, the virtual EXIT would become an orphan node. 
		 * What is more serious, the PDT built upon such CFG later on would have no head, causing failure in the construction of
		 * CDG (at least, the getInverseFullPath() routine would never terminate because of the lack of head/root of the PDT).
		 * 
		 * To overcome such an issue, we detect the infinite loop in the first place, and then treat the "GotoStmt" statements whose
		 * target is the first unit of the infinite loop ALL as tails, and then connect these tails to EXIT
		 */
		List<Unit> tailList = super.getTails();
		if (tailList.isEmpty()) {
			tailList = findTails();
			assert (!tailList.isEmpty());
		}
		//for (Unit tail : super.getTails()) {
		for (Unit tail : tailList) {
			List<Unit> tailPreds = new ArrayList<Unit>();
			tailPreds.addAll(this.getUnexceptionalPredsOf(tail));
			tailPreds.add(startStmt);
			unitToUnexceptionalPreds.put(tail, tailPreds);
			// create an edge from the Start to each tail
			succsOfStart.add(tail);
		}
		unitToUnexceptionalSuccs.put(startStmt, succsOfStart);
		unitToUnexceptionalPreds.put(startStmt, emptySet);
		// now the Start node becomes the sole head of this ACFG
		heads.add(startStmt);
		
		// HOWEVER, we can NOT insert this node before any ID Stmt !!
		//unitChain.addFirst(startStmt);
		Unit insPnt = utils.getFirstNonIdUnit(unitChain);
		if (null != insPnt) {
			unitChain.insertBefore(startStmt, insPnt);
		}
		else {
			unitChain.addLast(startStmt);
		}
		unitsToRemove.add(startStmt);
		
		// keep the unmodifiability of internal structures
		makeMappedListsUnmodifiable(unitToUnexceptionalSuccs);
		makeMappedListsUnmodifiable(unitToUnexceptionalPreds);
		if (body.getTraps().size() != 0) {
		    unitToSuccs = combineMapValues(unitToUnexceptionalSuccs, 
					   unitToExceptionalSuccs);
		    unitToPreds = combineMapValues(unitToUnexceptionalPreds, 
					   unitToExceptionalPreds);
		}
	}
	
	public List<Unit> getHeads() {
		return heads;
	}
	public List<Unit> getTails() {
		return tails;
		//return super.getTails();
	}
	
	/** Collect GotoStmts whose target is the first stmt of the infinite loop for CFGs having no tails because of the 
	 * presence of infinite loop, and treat them as tails
	 *  
	 */
	private List<Unit> findTails() {
		List<Unit> alltails = new ArrayList<Unit>();
		LoopNestTree lnt = new LoopNestTree(this.getBody());
		
		Stmt infLoopHead = null;
		Loop infLoop = null;
		for (Loop lp : lnt) {
			if (lp.loopsForever()) {
				infLoopHead = lp.getHead();
				infLoop = lp;
				break;
			}
		}
		
		if (null == infLoopHead) {
			// no infinite loop found...
			/*
			for (Loop lp : lnt) {
				System.out.println("Loop exits");
				for (Stmt s : lp.getLoopExits()) {
					System.out.println(s);
				}
			}
			*/
			infLoop = lnt.descendingSet().iterator().next();
			Loop outermostLoop = null;
			if (lnt.hasNestedLoops()) {
				Iterator<Loop> lit = lnt.descendingSet().iterator();
				boolean found = false;
				while (lit.hasNext()) {
					outermostLoop = lit.next();
					boolean fail = false;
					for (Loop lp : lnt) {
						if (lp == outermostLoop) continue;
						if (!outermostLoop.getLoopStatements().containsAll(lp.getLoopStatements())) {
							fail = true;
							break;
						}
					}
					if (!fail) {
						found = true;
						break;
					}
				}
				if (found) {
					infLoop = outermostLoop;
					infLoopHead = infLoop.getHead();
					for (Stmt s : infLoop.getLoopStatements()) {
						if (s instanceof GotoStmt) {
							Stmt tgt = (Stmt) ((GotoStmt)s).getTarget();
							if (tgt.equals(infLoopHead)) {
								alltails.add(s);
							}
						}
					}
					return alltails;
				}
			}
			// no outermost loop found either,  fall back to the naive search for the largest loop
			int msz = Integer.MIN_VALUE;
			for (Loop lp : lnt) {
				Stmt s = lp.getBackJumpStmt();
				if (s instanceof GotoStmt) {
					if ( ((GotoStmt)s).getTarget() == lp.getHead() ) {
						if (lp.getLoopStatements().size() > msz) {
							msz = lp.getLoopStatements().size();
							infLoop = lp;
						}
					}
				}
			}
		}
		
		infLoopHead = infLoop.getHead();
		System.out.println("InfLoopHead used: " + infLoopHead);
		
		// treat the tail GotoStmt of each loop that has its jumping back stmt pointed to the infLoopHead 
		// determined above as an exit of the cfg
		for (Unit u : this.getBody().getUnits()) {
			if (u instanceof GotoStmt) {
				if ( ((GotoStmt)u).getTarget() == infLoopHead ) {
					alltails.add(u);
				}
			}
		}
		
		return alltails;
	}
	
	public void dumpCFG() {
		utils.dumpUnitGraph(this);
	}
	
	public boolean hasNode(Unit node) {
		return unitToSuccs.containsKey(node) && unitToPreds.containsKey(node);
	}
	
	/** extended interface for updating the graph structure of the CFG */
	// remove a vertex from a CFG
	public void removeGraphNode(Unit node) {
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
				if (getSuccsOf(u)!=null) addToSuccs(u, d); //getSuccsOf(u).add(d);
				if (getPredsOf(d)!=null) addToPreds(d, u); // getPredsOf(d).add(u);
			}
		}
		
		// 2. update upwards
		for (Unit u : getPredsOf(node)) {
			//getSuccsOf(u).remove(node);
			removeFromSuccs(u, node);
		}
			
		// 3. update downwards
		for (Unit d : getSuccsOf(node)) {
			//getPredsOf(d).remove(node);
			removeFromPreds(d, node);
		}
		
		// 4. remove the node
		unitToPreds.remove(node);
		unitToSuccs.remove(node);
		
		this.unitChain.remove(node);
	}
	
	public void addToSuccs(Unit parent, Unit child) {
		if (!unitToSuccs.containsKey(parent)) return;
		List<Unit> succs = unitToSuccs.get(parent);
		if (succs.contains(child)) return;
		List<Unit> nsuccs = new ArrayList<Unit>(succs);
		nsuccs.add(child);
		unitToSuccs.put(parent, nsuccs);
	}
	public void removeFromSuccs(Unit parent, Unit child) {
		if (!unitToSuccs.containsKey(parent)) return;
		List<Unit> succs = unitToSuccs.get(parent);
		if (!succs.contains(child)) return;
		List<Unit> nsuccs = new ArrayList<Unit>(succs);
		nsuccs.remove(child);
		unitToSuccs.put(parent, nsuccs);
	}
	public void addToPreds(Unit parent, Unit child) {
		if (!unitToPreds.containsKey(parent)) return;
		List<Unit> preds = unitToPreds.get(parent);
		if (preds.contains(child)) return;
		List<Unit> npreds = new ArrayList<Unit>(preds);
		npreds.add(child);
		unitToPreds.put(parent, npreds);
	}
	public void removeFromPreds(Unit parent, Unit child) {
		if (!unitToPreds.containsKey(parent)) return;
		List<Unit> preds = unitToPreds.get(parent);
		if (!preds.contains(child)) return;
		List<Unit> npreds = new ArrayList<Unit>(preds);
		npreds.remove(child);
		unitToPreds.put(parent, npreds);
	}
}

/* vim :set ts=4 tw=4 tws=4 */
