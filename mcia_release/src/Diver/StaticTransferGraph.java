/**
 * File: src/Diver/StaticTransferGraph.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai		created; defining the value transfer graph, which models the static 
 *							value transfer relations inside and across methods
 * 06/26/13		hcai		complete draft of static VTG construction
 * 06/27/13		hcai		first runnable static analysis
 * 06/28/13		hcai		fix local alias classification assertions; correct arc direction for parameter edges
 * 07/02/13		hcai		fixed all static transfer edges, first workable static analysis
 * 07/04/13		hcai		finally serialization and deserialization of static VTG worked around
 * 07/06/13		hcai		factor out the VTG base as a template and made the static graph a descendant of it
 * 07/20/13		hcai		added missing Local edges connecting Defs of actual parameters to them; 
 * 07/21/13		hcai		removed "local alias edges" connecting variables across methods
 * 07/22/13		hcai		reached the complete workable version of CD-less Diver
 * 08/08/13		hcai		incorporated intraprocedural CDs to Diver, first version of stage-2 Diver reached
 * 08/12/13		hcai		adapted to per-CFG CDG for facilitating interprocedural CD computation and incorporation
 *							gave up the previous shared singleton object used for computing CDG for all methods
 * 08/16/13		hcai		incorporated interprocedural CDs to Diver, first version of stage-3 Diver reached
 * 08/21/13		hcai		added static VTG validation against any missing dependencies that involve object variables,
 *							including library objects, by comparing with static forward slice
 *							Also, added missing intraprocedural (Local) transfer edges where the source transfers value
 *							(LibCallObjs in particular) to the target NOT through assignments
 * 09/01/13		hcai		added creating interprocedural exceptional CDs due to uncaught exceptions
 * 01/07/15		hcai		added reachability analysis for heap-object value transfer edges (this analysis is not required when this 
 * 							static dependence model is used for dynamic analysis but can lead to too many false positive dependencies 
 * 							when used for static analysis directly (this is done when comparing SEA-based static IA against MDG-based)
 *  
*/
package Diver;

import java.io.*;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import dua.global.ProgramFlowGraph;
import dua.global.ReachabilityAnalysis;
import dua.global.dep.DependenceFinder;
import dua.global.dep.DependenceFinder.Dependence;
import dua.global.dep.DependenceGraph;
import dua.global.dep.DependenceFinder.NodePoint;
import dua.method.CFG;
import dua.method.CFGDefUses;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.NodeDefUses;
import dua.method.CFGDefUses.StdVariable;
import dua.method.CFGDefUses.ObjVariable;
import dua.method.ReachableUsesDefs;
import dua.method.CFGDefUses.Def;
import dua.method.CFGDefUses.Use;
import dua.method.CFGDefUses.Variable;
import dua.method.CallSite;
import dua.method.ReachableUsesDefs.FormalParam;
import dua.util.Pair;
import fault.StmtMapper;

import soot.*;
import soot.jimple.*;

import MciaUtil.*;
import MciaUtil.VTEdge.VTEType;

/** the static value transfer graph (VTG) that models value flow relations between variables, 
 * both intra- and inter-procedurally;
 *
 * VTG serves tracing value flow of variables that potentially propagates the impacts of original changes
 */
public class StaticTransferGraph extends ValueTransferGraph<SVTNode, SVTEdge> implements Serializable {
	/** a pair recording method and statement to be associated with a variable, used for recording 
	 *  the writer/reader of that variable 
	 */
	static final class methodStmtPair {
		private final SootMethod m;
		private final Stmt s;
		public methodStmtPair(SootMethod _m, Stmt _s) {
			m = _m; s = _s;
		}
		public SootMethod method() { return m; }
		public Stmt stmt() { return s; }
	}
	
	/* conservative read and write sets of global variables, namely static class fields in Java */
	transient final Map<Variable, Set<methodStmtPair>> globalWS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	transient final Map<Variable, Set<methodStmtPair>> globalRS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	
	/* conservative read and write sets of instance variables, namely class instance fields */
	transient final Map<Variable, Set<methodStmtPair>> insvWS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	transient final Map<Variable, Set<methodStmtPair>> insvRS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	
	/* conservative read and write sets of ArrayRefs, namely array elements */
	transient final Map<Variable, Set<methodStmtPair>> arrayEleWS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	transient final Map<Variable, Set<methodStmtPair>> arrayEleRS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	
	/* conservative read and write sets of Library objects, namely libObjs */
	transient final Map<Variable, Set<methodStmtPair>> libObjWS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	transient final Map<Variable, Set<methodStmtPair>> libObjRS = new LinkedHashMap<Variable, Set<methodStmtPair>>();
	
	/* the common initial Def set used for intraprocedural edge construction for any method */ 
	transient final List<SVTNode> preDefSet = new LinkedList<SVTNode>();
	/* the common initial local alias set used for intraprocedural edge construction for any method */
	transient final Map<Value, Set<SVTNode>> preLocalAliasSets = new LinkedHashMap<Value, Set<SVTNode>>();
	
	/* all reachable application methods - retrieve in advance for efficient later accesses */
	transient static Set<SootMethod> reachableMethods;
	
	boolean includeIntraCD = false;
	boolean includeInterCD = false;
	
	boolean addExceptionalInterCD = false;
	boolean ignoreRuntimeExceptionCD = false;
	
	/* control dependencies */
	transient final StaticInterCDGraphEx sICDGEx =  new StaticInterCDGraphEx();
	
	/* flow-sensitivity for heap edges */
	protected boolean heflowsens = false; 

	@Override protected void initInternals() {
		super.initInternals();
		reachableMethods = null;
	}
	public StaticTransferGraph() {
		super();
	}
	
	public void setHeFlowSens(boolean flowsens) {
		heflowsens = flowsens;
	}
	
	public void setIncludeInterCD(boolean interCD) {
		includeInterCD = interCD;
	}
	public void setIncludeIntraCD(boolean intraCD) {
		includeIntraCD = intraCD;
	}
	public void setExInterCD(boolean exInterCD) {
		addExceptionalInterCD = exInterCD;
	}
	public void setIgnoreRTECD(boolean ignoreRTECD) {
		ignoreRuntimeExceptionCD = ignoreRTECD;
	}
	
	@Override public String toString() {
		return "[Static] " + super.toString();
	}
	
	/** ! this function is ONLY used for separately adding CDG edges to VTG, namely
	 *	augmenting the CDless VTG after it got constructed;
	 * Therefore, this is mostly used just for Debugging purposes in Diver 
	 */
	protected static void addControlDependencies(boolean debugOut) {
		/* Intra-procedural control dependencies */
		final StaticCDGraphEx CDEx = new StaticCDGraphEx();
		CDEx.turnDebug(debugOut);
		//CDEx.joinTransferGraph(this);
		CDEx.computeAllCDs();
		CDEx.dumpInternals(debugOut);
	}
	
	/** a convenient routine for adding an edge and the covered nodes into the graph */
	/** a convenient routine for adding an edge and the covered nodes into the graph */
	private void createTransferEdge(Variable srcVar, SootMethod srcMethod, Stmt srcStmt,
															Variable tgtVar, SootMethod tgtMethod, Stmt tgtStmt, 
															VTEType etype) {
		createTransferEdge(srcVar, srcMethod, srcStmt, tgtVar, tgtMethod, tgtStmt, etype, true);
	}
	private void createTransferEdge(Variable srcVar, SootMethod srcMethod, Stmt srcStmt,
															Variable tgtVar, SootMethod tgtMethod, Stmt tgtStmt, 
															VTEType etype, boolean reachabilityCheck) {
		if (reachabilityCheck) {
			// any transfer edges associated with methods unreachable from entry should be ignored
			if ( !(reachableMethods.contains(srcMethod) && reachableMethods.contains(tgtMethod) ) ) {
				return;
			}
		}
		SVTNode src = new SVTNode(srcVar, srcMethod, srcStmt);
		SVTNode tgt = new SVTNode(tgtVar, tgtMethod, tgtStmt);
		
		createTransferEdge (src, tgt, etype);
	}
		
	protected void createTransferEdge(SVTNode src, SVTNode tgt, VTEType etype) {
		SVTEdge edge = new SVTEdge(src, tgt, etype);
		addEdge (edge);
	}
	
	protected void createTransferEdge(SVTNode src, SVTNode tgt, VTEType etype, boolean reachabilityCheck) {
		createTransferEdge(src.getVar(), src.getMethod(), src.getStmt(),
											tgt.getVar(), tgt.getMethod(), tgt.getStmt(), etype, reachabilityCheck);
	}
	
	public void addEdge(SVTEdge edge) {
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
	/**
	 * compute all possible writers and readers of components of heap objects, namely object fields and array elements
	 * @param debugOut if dumping debug info during the computations
	 * @return
	 */
	private int computeRWSets(boolean debugOut) {
		Iterator<SootClass> clsIt1 = Scene.v().getClasses().iterator();
		while (clsIt1.hasNext()) {
			SootClass sClass = (SootClass) clsIt1.next();
			
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
			//for (SootMethod sMethod : ProgramFlowGraph.inst().getReachableAppMethods()) {
				if ( !sMethod.isConcrete() ) {
					// skip abstract methods and phantom methods, and native methods as well
					continue; 
				}
				if ( sMethod.toString().indexOf(": java.lang.Class class$") != -1 ) {
					// don't handle reflections now either
					continue;
				}
				if (!reachableMethods.contains(sMethod)) {
					// skip unreachable methods
					continue;
				}
								
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				//Body body = sMethod.getActiveBody();
				Body body = sMethod.retrieveActiveBody();
				
				/* the ID of a method to be used for identifying and indexing a method in the event maps of EAS */
				//String meId = sClass.getName() +	"::" + sMethod.getName();
				String meId = sMethod.getSignature();
				// -- DEBUG
				if (debugOut) {
					System.out.println("\nWrite/Read analysis: now traversing method " + meId + "...");
				}
				
				PatchingChain<Unit> pchn = body.getUnits();
				//Chain<Local> locals = body.getLocals();
				
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);
				CFGDefUses cfgDUs = (CFGDefUses)cfg;
				
				/*
				 * collect reader and writer methods of all static and instance variables
				 */
				List<Def> fldDefs = cfgDUs.getFieldDefs();
				List<Use> fldUses = cfgDUs.getFieldUses();
				for (Def d : fldDefs) {
					assert d.getValue() instanceof FieldRef; 
					SootFieldRef dfr = ((FieldRef)d.getValue()).getFieldRef();
					SootField df = ((FieldRef)d.getValue()).getField();
					assert df == dfr.resolve();
					if (/*df.isFinal() ||*/ df.isPhantom()) {
						continue;
					}
					if (df.isFinal() && !df.getDeclaringClass().isApplicationClass() && d.getN().getStmt()==null) {
						// library object fields (System.out, say) that do not have definition statement associated with 
						if (debugOut) {
							System.out.println("Skipped static final system object field def: " + d);
						}
						continue;
					}
					/*
					if (d.isInCatchBlock()) {
						System.out.println("Got a field def in catch/finally block: " + d);
					}
					*/
					
					/* collect static variable writers */
					if (df.isStatic()) {
						Set<methodStmtPair> mspairs = globalWS.get(d.getVar());
						if (null == mspairs) {
							mspairs = new LinkedHashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
						globalWS.put(d.getVar(), mspairs);
					}
					else {
						Set<methodStmtPair> mspairs = insvWS.get(d.getVar());
						if (null == mspairs) {
							mspairs = new LinkedHashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
						insvWS.put(d.getVar(), mspairs);
					}
				}
				
				for (Use u : fldUses) {
					assert u.getValue() instanceof FieldRef; 
					SootFieldRef ufr = ((FieldRef)u.getValue()).getFieldRef();
					SootField uf = ((FieldRef)u.getValue()).getField();
					assert uf == ufr.resolve();
					if (/*uf.isFinal() ||*/ uf.isPhantom()) {
						continue;
					}
					if (uf.isFinal() && !uf.getDeclaringClass().isApplicationClass() && u.getN().getStmt()==null) {
						// library object fields (System.out, say) that do not have definition statement associated with 
						if (debugOut) {
							System.out.println("Skipped static final system object field use: " + u);
						}
						continue;
					}
					/*
					if (u.isInCatchBlock()) {
						System.out.println("Got a field use in catch/finally block: " + u);
					}
					*/
					
					/* collect static variable readers */
					if (uf.isStatic()) {
						Set<methodStmtPair> mspairs = globalRS.get(u.getVar());
						if (null == mspairs) {
							mspairs = new LinkedHashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
						globalRS.put(u.getVar(), mspairs);
					}
					else {
						Set<methodStmtPair> mspairs = insvRS.get(u.getVar());
						if (null == mspairs) {
							mspairs = new LinkedHashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
						insvRS.put(u.getVar(), mspairs);
					}
				} // for each field use
				
				/*
				 * collect reader and writer methods of all array elements (ArrayRefs)
				 */
				List<Def> aeDefs = cfgDUs.getArrayElemDefs();
				List<Use> aeUses = cfgDUs.getArrayElemUses();
				for (Def d : aeDefs) {
					assert d.getValue() instanceof ArrayRef; 
					ArrayRef ar = (ArrayRef)d.getValue();
					/*
					if (d.isInCatchBlock()) {
						System.out.println("Got a arrayElement def in catch/finally block: " + d);
					}
					*/

					/* collect array element  writers */
					Set<methodStmtPair> mspairs = arrayEleWS.get(d.getVar());
					if (null == mspairs) {
						mspairs = new LinkedHashSet<methodStmtPair>();
					}
					mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
					arrayEleWS.put(d.getVar(), mspairs);
				}
				
				for (Use u : aeUses) {
					assert u.getValue() instanceof ArrayRef; 
					ArrayRef ar = (ArrayRef)u.getValue();
					/*
					if (u.isInCatchBlock()) {
						System.out.println("Got a arrayElement use in catch/finally block: " + u);
					}
					*/
					
					Set<methodStmtPair> mspairs = arrayEleRS.get(u.getVar());
					if (null == mspairs) {
						mspairs = new LinkedHashSet<methodStmtPair>();
					}
					mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
					arrayEleRS.put(u.getVar(), mspairs);
				} // for all each array element use
				
				/*
				 * collect reader and writer methods of all library objects
				 */
				// separately do this in addLibObjRWSets
				
			} // for each method
		} // for each class
		
		return 0;
	}
	
	private void initPreDefSetAndLocalAliasSet() {
		/* defs, of class Field Refs, coming from static class variables */
		for (Map.Entry<Variable, Set<methodStmtPair>> en : globalWS.entrySet()) {
			methodStmtPair firstPair = null;
			for (methodStmtPair mp : en.getValue()) {
				preDefSet.add(new SVTNode(en.getKey(), mp.method(), mp.stmt()));
				if (null == firstPair) {
					firstPair = mp;
				}
			}
			
			assert firstPair != null;
			if (en.getKey().getValue().getType() instanceof RefLikeType) {
				preLocalAliasSets.put(en.getKey().getValue(), new LinkedHashSet<SVTNode>());
				preLocalAliasSets.get(en.getKey().getValue()).add(
						new SVTNode( en.getKey()/*new StdVariable(en.getKey().getValue())*/, firstPair.method(), firstPair.stmt()));
			}
		}
		/* defs, of object Field Refs, coming from instance variables */
		for (Map.Entry<Variable, Set<methodStmtPair>> en : insvWS.entrySet()) {
			methodStmtPair firstPair = null;
			for (methodStmtPair mp : en.getValue()) {
				preDefSet.add(new SVTNode(en.getKey(), mp.method(), mp.stmt()));
				if (null == firstPair) {
					firstPair = mp;
				}
			}
			
			assert firstPair != null;
			if (en.getKey().getValue().getType() instanceof RefLikeType) {
				preLocalAliasSets.put(en.getKey().getValue(), new LinkedHashSet<SVTNode>());
				preLocalAliasSets.get(en.getKey().getValue()).add(
						new SVTNode( en.getKey()/*new StdVariable(en.getKey().getValue())*/, firstPair.method(), firstPair.stmt()));
			}
		}
		/** for defs, of array elements, we don't add them to the preliminary "initial defSet / localAliasSet" because they won't
		 * be escaping out of a method independently (namely, must escape via class/instance fieldRefs, and we already treat 
		 * fieldRefs of all kinds above. 
		 */
	}
	
	/** An alternative, brute-force, way of computing library object read/write transfers 
	 *  Another, more efficient, way is to do this in createIntraproceduralValueTransferEdges: for library objects, specially 
	 *  compute transfers both intra- and inter-procedurally 
	 */
	void addLibObjRWSets(boolean debugOut) {
		Iterator<SootClass> clsIt1 = Scene.v().getClasses().iterator();
		while (clsIt1.hasNext()) {
			SootClass sClass = (SootClass) clsIt1.next();
			
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
			//for (SootMethod sMethod : ProgramFlowGraph.inst().getReachableAppMethods()) {
				if ( !sMethod.isConcrete() ) {
					// skip abstract methods and phantom methods, and native methods as well
					continue; 
				}
				if ( sMethod.toString().indexOf(": java.lang.Class class$") != -1 ) {
					// don't handle reflections now either
					continue;
				}
				if (!reachableMethods.contains(sMethod)) {
					// skip unreachable methods
					continue;
				}
								
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				//Body body = sMethod.getActiveBody();
				Body body = sMethod.retrieveActiveBody();
				
				/* the ID of a method to be used for identifying and indexing a method in the event maps of EAS */
				//String meId = sClass.getName() +	"::" + sMethod.getName();
				String meId = sMethod.getSignature();
				// -- DEBUG
				if (debugOut) {
					System.out.println("\nLibrary Object Write/Read analysis: now traversing method " + meId + "...");
				}
				
				PatchingChain<Unit> pchn = body.getUnits();
				//Chain<Local> locals = body.getLocals();
				
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);
				CFGDefUses cfgDUs = (CFGDefUses)cfg;
				
				/*
				 * collect reader and writer methods of all library objects
				 */
				List<Def> loDefs = cfgDUs.getLibObjDefs();
				List<Use> loUses = cfgDUs.getLibObjUses();
				for (Def d : loDefs) {
					assert d.getVar().isObject();
					if (d.getN().getStmt()==null) {
						// library objects (PrintStream, say) that do not have definition statement associated with 
						if (debugOut) {
							System.out.println("Skipped static final system object field use: " + d);
						}
						continue;
					}

					/* collect library object  writers */
					Set<methodStmtPair> mspairs = libObjWS.get(d.getVar());
					if (null == mspairs) {
						mspairs = new LinkedHashSet<methodStmtPair>();
					}
					mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
					libObjWS.put(d.getVar(), mspairs);
				}
				
				for (Use u : loUses) {
					assert u.getVar().isObject(); 
					if (u.getN().getStmt()==null) {
						// library objects (PrintStream, say) that do not have definition statement associated with 
						if (debugOut) {
							System.out.println("Skipped static final system object field use: " + u);
						}
						continue;
					}
					
					Set<methodStmtPair> mspairs = libObjRS.get(u.getVar());
					if (null == mspairs) {
						mspairs = new LinkedHashSet<methodStmtPair>();
					}
					mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
					libObjRS.put(u.getVar(), mspairs);
				} // for each library object use
			} // for each method
		} // for each class
		
		for (Variable v:libObjWS.keySet()) {
			/* no paired read-write, no edge */
			/*
			if (!libObjWS.containsKey(v)) {
				continue;
			}
			*/
			List<Variable> rvs = new LinkedList<Variable>();
			for (Variable rv : libObjRS.keySet()) {
				if (v.mayEqualAndAlias(rv)) {
					rvs.add(rv);
				}
			}
			if (rvs.isEmpty()) {
				continue;
			}
			
			for (methodStmtPair mspSrc : libObjWS.get(v)) {
				for (Variable rv : rvs) {
					for (methodStmtPair mspTgt : libObjRS.get(rv)) {
						if (mspSrc.method().equals(mspTgt.method())) {
							/* avoid self-edges here because they have already been created as IntraproceduralTransferEdges */
							continue;
						}
						
						List<Pair<Def,Integer>> defs4use = DependenceFinder.getAllDefsForUse(rv, ProgramFlowGraph.inst().getNode( mspTgt.stmt()) );
						boolean real = false;
						for (Pair<Def,Integer> pair : defs4use) {
							Def d = pair.first();
							if (d.getVar().equals(v)) { real = true; break; }
						}
						if (!real) continue;
						
						createTransferEdge(varAbstraction(v,mspSrc.method()), mspSrc.method(), mspSrc.stmt(), 
								varAbstraction(rv,mspTgt.method()), mspTgt.method(), mspTgt.stmt(), VTEType.VTE_LIBOBJ);
					}
				}
			}
		}
	}
	
	/** build the VTG of the classes loaded by Soot for analysis
	 * @param debugOut true for logging internal steps and notices during the graph construction
	 * @return 0 for success, otherwise, exception thrown tells error messages
	 */ 
	public int buildGraph(boolean debugOut) throws Exception {
		/** the reachable methods retrieved by ProgramFlowGraph are actual those only when "-reachablility" option is enable
		 * However, when that option is set, this facility will ignore all call sites in catch blocks when collecting CFGs;
		 * to bypass this conflict of interest, use the reachable methods retrieved separately using Soot only, as is implemented in 
		 * MciaUtil.utils 
		 */
		reachableMethods = new LinkedHashSet<SootMethod>(); 
		reachableMethods.addAll(ProgramFlowGraph.inst().getReachableAppMethods());
		//reachableMethods = utils.getReachableMethodsFromEntries(true);
		
		/* traverse all classes - the first pass, for computing write and read sets of object fields and array elements */
		computeRWSets(debugOut);
		
		/* create the initial Def set and local alias set common to intraprocedural edge construction in any reachable CFG */
		initPreDefSetAndLocalAliasSet();
		
		// the computation of Interprocedural CDs relies on the intraprocedural CDs and must come after all intraCDs got ready
		if (includeIntraCD && includeInterCD) {
			/* initialize the agent for computing control dependencies */
			sICDGEx.turnDebug(debugOut);
			sICDGEx.turnHolisticCDG(/*true*/false); // we do not the holistic interprocedural CDG for Diver at least for now
			sICDGEx.turnSymbolicCD(false);
			sICDGEx.joinTransferGraph(this);
			sICDGEx.turnMemoryForSpeed(true);
			
			// regarding the addition of exceptional interprocedural CDs due to uncaught exceptions
			sICDGEx.turnExceptionalInterCD(addExceptionalInterCD);
			sICDGEx.turnIgnoreRTECD(ignoreRuntimeExceptionCD);
		}
				
		/* traverse all classes - the second pass, creating all transfer edges */
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
			//for (SootMethod sMethod : ProgramFlowGraph.inst().getReachableAppMethods()) {
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
				if (!reachableMethods.contains(sMethod)) {
					// skip unreachable methods
					continue;
				}
				
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				//Body body = sMethod.getActiveBody();
				Body body = sMethod.retrieveActiveBody();
				
				/* the ID of a method to be used for identifying and indexing a method in the event maps of EAS */
				//String meId = sClass.getName() +	"::" + sMethod.getName();
				String meId = sMethod.getSignature();
				// -- DEBUG
				if (debugOut) {
					System.out.println("\nVTG construction: now processing method " + meId + "...");
				}
				
				PatchingChain<Unit> pchn = body.getUnits();
				//Chain<Local> locals = body.getLocals();
				
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);
				CFGDefUses cfgDUs = (CFGDefUses)cfg;
				
				/*
				 * 1. prepare for static and instance variable value flow edges, ignoring 
				 * "final" variables because there are not writable thus not involve in transferring impacts
				 */
				/*
				List<Def> fldDefs = cfgDUs.getFieldDefs();
				List<Use> fldUses = cfgDUs.getFieldUses();
 				for (Def d : fldDefs) {
					assert d.getValue() instanceof FieldRef; 
					SootFieldRef dfr = ((FieldRef)d.getValue()).getFieldRef();
					SootField df = ((FieldRef)d.getValue()).getField();
					assert df == dfr.resolve();
					if (df.isFinal() || df.isPhantom()) {
						continue;
					}
					if ( !isInstanceVarOfThis(d.getValue(), sClass) ) {
						// not a InstanceFeildRef to the current class's field 
						continue;
					}
					
					// collect static variable writers
					if (df.isStatic()) {
						Set<methodStmtPair> mspairs = globalWS.get(d.getVar());
						if (null == mspairs) {
							mspairs = new HashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
						globalWS.put(d.getVar(), mspairs);
					}
					// collect instance variable writers, regardless of its access permission - public/protected/private, of the variable
					else {
						Set<methodStmtPair> mspairs = insvWS.get(d.getVar());
						if (null == mspairs) {
							mspairs = new HashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
						insvWS.put(d.getVar(), mspairs);
					}
				}
				
				for (Use u : fldUses) {
					assert u.getValue() instanceof FieldRef; 
					SootFieldRef ufr = ((FieldRef)u.getValue()).getFieldRef();
					SootField uf = ((FieldRef)u.getValue()).getField();
					assert uf == ufr.resolve();
					if (uf.isFinal() || uf.isPhantom()) {
						continue;
					}
					if ( !isInstanceVarOfThis(u.getValue(), sClass) ) {
						// not a InstanceFeildRef to the current class's field
						continue;
					}
					
					// collect static variable readers
					if (uf.isStatic()) {
						Set<methodStmtPair> mspairs = globalRS.get(u.getVar());
						if (null == mspairs) {
							mspairs = new HashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
						globalRS.put(u.getVar(), mspairs);
					}
					// collect instance variable readers, regardless of its access permission - public/protected/private, of the variable
					else {
						Set<methodStmtPair> mspairs = insvRS.get(u.getVar());
						if (null == mspairs) {
							mspairs = new HashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
						insvRS.put(u.getVar(), mspairs);
					}
				}
				*/
				
				// -
				/*
				 * 2. parameter value flow edges, from actual parameter to formal parameter
				 * 
				 * Note: for parameters passed by "reference" (not really in terms of terminology but 
				 * of the semantics, namely the caller will see the changes made to the parameter in the callee),
				 * we simply treat them as "returns" 
				 */
				createParameterTransferEdges(cfg);
				
				/*
				 * 3. return value flow edges, from return statements at callee back to assignment 
				 * statement that receives the return value at call sites in caller
				 */
				createReturnValueTransferEdges(cfg);
				
				/*
				 * 4. intraprocedural value transfer edges, from each def da to another def db 
				 * that is dependent on da
				 */
				/* initial definition set */
				List<SVTNode> defSet = new LinkedList<SVTNode>();
				createIntraproceduralValueTransferEdges(cfg, defSet/*, globalWS, insvWS*/);
				
				/*
				 * 5. control dependence transfer edges, from defs of used var at the CD edge source to the used var
				 *  at the CD edge target 
				 */
				/** a lame design for now: use the initial definition set, computed during the 
				 * construction of Intraprocedural Value transfer edges, for computing an exhaustive set 
				 * of Control transfer edges based on a basic CD edge pointing from stmt a to stmt b
				 */
				/* Intra-procedural control dependencies */
				if (includeIntraCD) {
					final StaticCDGraphEx CDGEx = new StaticCDGraphEx();
					CDGEx.joinTransferGraph(this);
					CDGEx.turnDebug(debugOut);
					CDGEx.turnSymbolicCD(false);
					CDGEx.setCurDefSet(defSet);
					CDGEx.compuateIntraproceduralCDs(sMethod, null);
					
					/* Preparation for computing Inter-procedural control dependencies */
					if (includeInterCD) {
						sICDGEx.setMethodCDG(sMethod, CDGEx);
					}
				}
			}
		}
		
		/*
		 * 5. create instance variable value transfer edges across all application classes
		 */
		for (Variable v:insvWS.keySet()) {
			/* no paired read-write, no edge */
			/*
			if (!insvRS.containsKey(v)) {
				continue;
			}
			*/
			List<Variable> rvs = new LinkedList<Variable>();
			for (Variable rv : insvRS.keySet()) {
				if (v.mayEqualAndAlias(rv)) {
					rvs.add(rv);
				}
			}
			if (rvs.isEmpty()) {
				continue;
			}
			
			for (methodStmtPair mspSrc : insvWS.get(v)) {
				for (Variable rv : rvs) {
					for (methodStmtPair mspTgt : insvRS.get(rv)) {
						if (mspSrc.method().equals(mspTgt.method())) {
							/* avoid self-edges here because they have already been created as IntraproceduralTransferEdges */
							continue;
						}
						
						if (this.heflowsens) {
							// add flow-sensitivity - even more precise way is to do this at statement level, which is more expensive 
							if (!ReachabilityAnalysis.forwardReaches(mspSrc.method(), mspTgt.method()) &&
								!ReachabilityAnalysis.forwardReaches(mspTgt.method(), mspSrc.method()) ) {
								continue;
							}
						}
						
						createTransferEdge(varAbstraction(v,mspSrc.method()), mspSrc.method(), mspSrc.stmt(), 
								varAbstraction(rv,mspTgt.method()), mspTgt.method(), mspTgt.stmt(), VTEType.VTE_INSVAR);
					}
				}
			}
		}
		
		/*
		 * 6. create array element value transfer edges across all application classes
		 */
		for (Variable v:arrayEleWS.keySet()) {
			/* no paired read-write, no edge */
			/*
			if (!arrayEleWS.containsKey(v)) {
				continue;
			}
			*/
			List<Variable> rvs = new LinkedList<Variable>();
			for (Variable rv : arrayEleRS.keySet()) {
				if (v.mayEqualAndAlias(rv)) {
					rvs.add(rv);
				}
			}
			if (rvs.isEmpty()) {
				continue;
			}
			
			for (methodStmtPair mspSrc : arrayEleWS.get(v)) {
				for (Variable rv : rvs) {
					for (methodStmtPair mspTgt : arrayEleRS.get(rv)) {
						if (mspSrc.method().equals(mspTgt.method())) {
							/* avoid self-edges here because they have already been created as IntraproceduralTransferEdges */
							continue;
						}
						
						if (this.heflowsens) {
							// add flow-sensitivity - even more precise way is to do this at statement level, which is more expensive
							if (!ReachabilityAnalysis.forwardReaches(mspSrc.method(), mspTgt.method()) &&
								!ReachabilityAnalysis.forwardReaches(mspTgt.method(), mspSrc.method()) ) {
								continue;
							}
						}
						
						createTransferEdge(varAbstraction(v,mspSrc.method()), mspSrc.method(), mspSrc.stmt(), 
								varAbstraction(rv,mspTgt.method()), mspTgt.method(), mspTgt.stmt(), VTEType.VTE_ARRAYELE);
					}
				}
			}
		}
		
		/*
		 * 7. create library object value transfer edges across all application classes
		 */
		//this.addLibObjRWSets(debugOut);
		
		/*
		 * 8. create static variable value transfer edges for the subject as a whole, involving
		 * all possible application classes 
		 */
		for (Variable v:globalWS.keySet()) {
			/*
			if (!globalRS.containsKey(v)) {
				// no paired read-write, no edge
				continue;
			}
			*/
			List<Variable> rvs = new LinkedList<Variable>();
			for (Variable rv : globalRS.keySet()) {
				if (v.mayEqualAndAlias(rv)) {
				//if (v.equals(rv)) {
					rvs.add(rv);
				}
			}
			if (rvs.isEmpty()) {
				continue;
			}
			
			for (methodStmtPair mspSrc : globalWS.get(v)) {
				for (Variable rv : rvs) {
					for (methodStmtPair mspTgt : globalRS.get(rv)) {
						if (mspSrc.method().equals(mspTgt.method())) {
							/* avoid self-edges here because they have already been created as IntraproceduralTransferEdges */
							continue;
						}
						
						if (this.heflowsens) {
							// add flow-sensitivity - even more precise way is to do this at statement level, which is more expensive 
							if (!ReachabilityAnalysis.forwardReaches(mspSrc.method(), mspTgt.method()) &&
								!ReachabilityAnalysis.forwardReaches(mspTgt.method(), mspSrc.method()) ) {
								continue;
							}
						}
						
						createTransferEdge(varAbstraction(v,mspSrc.method()), mspSrc.method(), mspSrc.stmt(), 
								varAbstraction(v,mspTgt.method()), mspTgt.method(), mspTgt.stmt(), VTEType.VTE_STVAR);
					}
				}
			}
		}
		
		/* 
		 * 9. consider computing interprocedural control dependencies and incorporating them into the now prepared static VTG
		 * Now that, if chosen, all intraCDs have been ready, add interprocedural control dependencies, 
		 * which are grounded upon those intraCDs in terms of computation, if chosen 
		 */
		if (includeIntraCD && includeInterCD) {
			// -- DEBUG
			if (debugOut) {
				System.out.println("\nVTG construction: now computing interprocedural CDs......");
			}
			sICDGEx.computeAllInterCDs();
		}
		
		return 0;
	}
	public static Variable makeVariable(Value val, Stmt s) {
		Variable v = null;
		if (val instanceof AnyNewExpr || val instanceof StringConstant || 
				val instanceof ClassConstant || val instanceof InvokeExpr) {
			CFGNode cfgn = ProgramFlowGraph.inst().getNode(s);
			v = new ObjVariable(val, cfgn);
		}
		else {
			v = new StdVariable(val);
		}
		return v;
	}
	private void createParameterTransferEdges(CFG cfg) {
		List<CallSite> cses = cfg.getCallerSites();
		for (CallSite cs : cses) {
			/*
			if (cs.isInCatchBlock()) {
				System.out.println("Got a caller site in catch/finally block: " + cs);
			}
			*/
			int naParams = cs.getNumActualParams();
			InvokeExpr iex = cs.getLoc().getStmt().getInvokeExpr();
			int startArgIdx = 0;
			if (iex instanceof InstanceInvokeExpr /*&& cs.isInstanceCall()*/) {
				startArgIdx = 1;
			}
			if (naParams < 1+startArgIdx || cfg.getMethod().getParameterCount() < 1) {
				// skip call sites with empty parameter list
				continue;
			}
			/* if there are multiple callees on the call site, we need link from the actual parameters
			 * to the formal parameters of each callee, conservatively for safety
			 */
			List<SootMethod> appCallees = cs.getAppCallees();
			for (SootMethod ce : appCallees) {
				if (!ce.equals(cfg.getMethod())) {
					// connect the caller to the right callee
					continue;
				}
				ReachableUsesDefs rudce = (ReachableUsesDefs) ProgramFlowGraph.inst().getCFG(ce);
				int nfParams = rudce.getNumFormalParams();
				assert naParams == nfParams;

				/* an edge per actual-formal parameter pair, the first pair connecting an object to the this pointer for
				 *  instance calls should be ignored
				 */
				int i = 0;
				for(i=startArgIdx; i<nfParams; i++) {
					Stmt sIdFormal = rudce.getFormalParam(i).getIdStmt();
					Value aval = cs.getActualParam(i);
					/** use StdVariable instead of CSArgVar to facilitate the graph connectivity modeling*/
					//Variable avar = new CSArgVar(aval, cs, i);
					Variable avar = makeVariable(aval, cs.getLoc().getStmt()); //new StdVariable(aval);
					Value fval = rudce.getFormalParam(i).getV();
					//Variable fvar = new CSArgVar(fval, cs, i); // here cs serves a place-holder only
					Variable fvar = makeVariable(fval, sIdFormal); //new StdVariable(fval);
					
					//assert cfg.getMethod() != cs.getLoc().getMethod();
					createTransferEdge(varAbstraction(avar,cs.getLoc().getMethod()), cs.getLoc().getMethod(), cs.getLoc().getStmt(), 
							varAbstraction(fvar,ce), ce, sIdFormal, VTEType.VTE_PARAM);
				} // for each parameter
			} // for each app callee
		} // for each call site
	} // createParameterTransferEdge
	
	private void createReturnValueTransferEdges(CFG cfg) {
		SootMethod m = cfg.getMethod();
		if (m.getReturnType() instanceof VoidType) {
			/* skip if this method has merely a "void" return */
			return;
		}
		List<CallSite> callerSites = cfg.getCallerSites();
		for (CallSite caller : callerSites) {
			SootMethod mCaller = caller.getLoc().getMethod();
			ReachableUsesDefs rudcaller = (ReachableUsesDefs)ProgramFlowGraph.inst().getCFG(mCaller);
			Stmt sCaller = caller.getLoc().getStmt();
			InvokeExpr iex = sCaller.getInvokeExpr();
			if (iex.getType().equals(VoidType.v())) {
				/* nothing is returned */
				continue;
			}
			assert !(sCaller instanceof ReturnStmt);
			if (!(sCaller instanceof AssignStmt)) {
				/* return value is not taken */
				continue;
			}
			/* returned variable whose value is used in the caller site */ 
			/** use StdVariable instead of CSReturnedVar to facilitate the graph connectivity modeling*/
			//CSReturnedVar csretVar = new CSReturnedVar(iex, caller);
			
			//StdVariable csretVar = new StdVariable( ((AssignStmt)sCaller).getLeftOp() );
			Variable csretVar = makeVariable( ((AssignStmt)sCaller).getLeftOp(), sCaller );
			
			/* we need link each possible return in this method to the caller site */
			List<CFGNode> cfgnodes = cfg.getNodes(); //	cfg.getFirstRealNonIdNode().getSuccs();
			for (CFGNode _node : cfgnodes) {
				if (_node.isSpecial()) {
					continue;
				}
				Stmt s = _node.getStmt();
				if (s instanceof IdentityStmt) {
					continue;
				}
				NodeDefUses node = (NodeDefUses)_node;
				if (!(s instanceof ReturnStmt)) {
					/* just capture every return statement */
					continue;
				}
				/** use StdVariable instead of ReturnVar to facilitate the graph connectivity modeling*/
				//ReturnVar rVar = new ReturnVar( ((ReturnStmt)s).getOp(), node );
				Variable rVar = null;
				Value retv = ((ReturnStmt)s).getOp();
				rVar = makeVariable(retv, s); //new StdVariable(retv);
				
				createTransferEdge(varAbstraction(rVar,m), m, s, varAbstraction(csretVar,mCaller), mCaller, sCaller, VTEType.VTE_RET);
				
			} // for each CFG node in the callee, namely the method under visit
		} // for each caller site of the method under visit
	} // createReturnValueTransferEdge
	
	/** a helper function, searching alias set according to any alias node, for createIntraproceduralValueTransferEdges */
	private Set<SVTNode> getAliasSet(Map<Value, Set<SVTNode>> aliasSets, Value a) {
		for(Map.Entry<Value, Set<SVTNode>> en : aliasSets.entrySet()) {
			for (SVTNode vn : en.getValue()) {
				if (dua.util.Util.valuesEqual(vn.getVar().getValue(), a, true)) {
					return en.getValue();
				}
			}
		}
		return null;
	}
	/** a helper function, searching the most recent def of a variable in the given def set, with aliasing considered */
	private SVTNode getRecentDef(List<SVTNode> defSet, Variable v) {
		ListIterator<SVTNode> iter = defSet.listIterator(defSet.size());
		while (iter.hasPrevious()) {
			SVTNode d = iter.previous();
			/*
			 * for array elements or object fields, we use "mayEqual" as the predicate to match the recent definition, which ignores
			 * the hosting object or array index, as is what we are supposed to do
			 */
			//if (dua.util.Util.valuesEqual(d.getVar().getValue(), v.getValue(), true)) {
			if (v.getValue() instanceof FieldRef || v.getValue() instanceof ArrayRef) {
				if(d.getVar().mayEqualAndAlias(v)) {
					return d;
				}
			}
			else { /* for locals, we match the definition by strict equality */
				if (d.getVar().equals(v)) {
					return d;
				}
			}
		}
		return null;
	}
	/** a helper function, searching all intraprocedural defs of a variable, for createIntraproceduralValueTransferEdges */
	public static Set<SVTNode> getAllDefs(List<SVTNode> defSet, Variable use, SootMethod m, CFGNode node) {
		return getAllDefs(defSet, use, m, node, false);
	}
	public static Set<SVTNode> getAllDefs(List<SVTNode> defSet, Variable use, SootMethod m, CFGNode node, boolean bLibObj) {
		Variable v = varAbstraction(use,m);
		/** get all defs of use in formal parameters and static/instance variable writers */
		ListIterator<SVTNode> iter = defSet.listIterator(defSet.size());
		Set<SVTNode> defs = new LinkedHashSet<SVTNode>();
		while (iter.hasPrevious()) {
			SVTNode d = iter.previous();
			/*
			 * for array elements or object fields, we use "mayEqual" as the predicate to match the recent definition, which ignores
			 * the hosting object or array index, as is what we are supposed to do
			 */
			//if (dua.util.Util.valuesEqual(d.getVar().getValue(), v.getValue(), true)) {
			if (v.getValue() instanceof FieldRef || v.getValue() instanceof ArrayRef /* || (bLibObj &&use.isObject())*/) {
				if(d.getVar().mayEqualAndAlias(v)) {
					defs.add(d);
				}
			}
			else { /* for locals, we match the definition by strict equality */
				if (d.getVar().equals(v)) {
					defs.add(d);
				}
			}
		}
		/** get all defs of use besides those in formal parameters and static/instance variable writers */
		Set<SVTNode> allDefs = new LinkedHashSet<SVTNode>();
		List<Pair<Def,Integer>> defs4use = DependenceFinder.getAllDefsForUse(use, node);
		for (Pair<Def,Integer> pair : defs4use) {
			CFGNode dn = pair.first().getN();
			SootMethod dm = ProgramFlowGraph.inst().getContainingMethod(dn);
			/*
			if (null == dm) {
				System.out.println("cannot find containing method for " + dn);
			}
			*/
			Def d = pair.first();
			Variable vd = d.getVar();
			if ( null != dm && (dm.equals(m) || (bLibObj && use.isObject()&&vd.isObject())) ) {
				//System.out.println("def for use " + use.getValue() + " : " + pair.first().getN().getStmt());
				
				if (vd.getValue() instanceof FieldRef || vd.getValue() instanceof ArrayRef || 
						(bLibObj && use.isObject() && vd.isObject() && !dm.equals(m) ) ) {
					if (vd.mayEqualAndAlias(use)) allDefs.add( new SVTNode(varAbstraction(vd,dm), dm, d.getN().getStmt()) );
				}
				else {
					if (vd.equals(use)) allDefs.add( new SVTNode(varAbstraction(vd,dm), dm, d.getN().getStmt()) );
				}
			}
		}
		
		allDefs.addAll(defs);
		return allDefs;
	}
	
	/** a helper function, abstracting a variable into simpler form if it is object field or array element, for 
	 * createIntraproceduralValueTransferEdges;
	 * - for object field, ignore object and just take the field;
	 * - for array element, ignore index/element and just take the array 
	 */
	public static Variable varAbstraction(Variable v, SootMethod m) {
		if (v.isArrayRef()) {
			/* for array element, we take the base only and strip out other components, which is an array */
			assert v.getBaseLocal().getType() instanceof ArrayType;
			return new StdVariable( v.getBaseLocal() );
		}
		
		if (v.isFieldRef()) {
			/* for object field, we ignore the host object and take the field only */
			return v;
			/*
			FieldRef fr = (FieldRef)v.getValue();
			return new StdVariable ( Jimple.v().newLocal(getCanonicalFieldName(v), fr.getField().getType()) );
			
			if (!isInstanceVarOfThis(v.getValue(), m.getDeclaringClass()) &&
					!fr.getField().isStatic() && !fr.getField().isFinal()) {
				return new StdVariable ( Jimple.v().newLocal(getCanonicalFieldName(v), fr.getField().getType()) );
			}
			else {
				return v;
			}
			*/
		}
		
		/* Locals if v is a L-value; otherwise can be other kinds of values such as Constant, Expr, etc.*/
		return v;
	}
	/**
	 * create Local edges for a given call site in the specified method, connecting, for each actual parameter, 
	 * each of the definitions of it in the method to the call site with respect to that parameter (the corresponding Use)
	 */
	private void createLocalEdgesForCallSite(List<SVTNode> defSet, SootMethod m, CallSite cs, CFGNode node) {
		int naParams = cs.getNumActualParams();
		InvokeExpr iex = cs.getLoc().getStmt().getInvokeExpr();
		int startArgIdx = 0;
		if (iex instanceof InstanceInvokeExpr /*&& cs.isInstanceCall()*/) {
			startArgIdx = 1;
		}
		if (naParams < 1+startArgIdx || !cs.hasAppCallees()) {
			// nothing to do with call site with empty parameter list (disregarding "this" for instance calls)
			return;
		}
		/* if there are multiple callees on the call site, we DO NOT need link from the definitions of actual parameters
		 * to the parameters of EACH callee, since we only care about each of the actual parameters at this call site; no matter how many
		 * callees at this site and what they are, the actual parameters are shared among them
		 */
		int i = 0;
		for(i=startArgIdx; i<naParams; i++) {
			Value aval = cs.getActualParam(i);
			Variable avar = makeVariable(aval,cs.getLoc().getStmt());// new StdVariable(aval);
			
			Set<SVTNode> allDefs = getAllDefs(defSet, avar, m, node);
			
			for (SVTNode rd : allDefs) {
				// For a flow-insensitive analysis, create a Local transfer edge from each of the defs of useVar to it
				createTransferEdge(varAbstraction(rd.getVar(),rd.getMethod()), rd.getMethod(), rd.getStmt(), 
						varAbstraction(avar,m), m, cs.getLoc().getStmt(), VTEType.VTE_INTRA);
			}
		} // for each actual parameter
	} // createLocalEdgesForCallSite
	/**
	 * create Local edges for a return stmt in the specified method, connecting each of the 
	 * definitions of it in the method to that return stmt
	 */
	private void createLocalEdgesForReturnStmt(List<SVTNode> defSet, SootMethod m, ReturnStmt s, CFGNode node) {
		Variable rvar = makeVariable(s.getOp(), s);// new StdVariable(aval);
		Set<SVTNode> allDefs = getAllDefs(defSet, rvar, m, node);
		for (SVTNode rd : allDefs) {
			// For a flow-insensitive analysis, create a Local transfer edge from each of the defs of useVar to it
			createTransferEdge(varAbstraction(rd.getVar(),rd.getMethod()), rd.getMethod(), rd.getStmt(), 
					varAbstraction(rvar,m), m, s, VTEType.VTE_INTRA);
		}
	} // createLocalEdgesForReturnStmt
	private void createIntraproceduralValueTransferEdges(CFG cfg, List<SVTNode> defSet
			/*, Map<Variable, Set<methodStmtPair>> globalWS, Map<Variable, Set<methodStmtPair>> insvWS*/) {
		SootMethod m = cfg.getMethod();
		ReachableUsesDefs rudce = (ReachableUsesDefs) cfg; //ProgramFlowGraph.inst().getCFG(m);
		Map<SVTNode, Integer> refParams = new LinkedHashMap<SVTNode, Integer>();
		int nfParams = rudce.getNumFormalParams();
		int startArgIdx = 0;
		/* skip the first parameter if this is an instance method, which will be the this reference then*/
		if (!m.isStatic()) {
			startArgIdx = 1;
		}
		
		/* the local alias sets of incoming allocation site, through parameters of reference type, 
		 * and local allocation sites 
		 */
		//Map<AllocSite, Set<SVTNode>> localAliasSets = new HashMap<AllocSite, Set<SVTNode>>();
		Map<Value, Set<SVTNode>> localAliasSets = new LinkedHashMap<Value, Set<SVTNode>>();
		
		/* defs, including FieldRefs and ArrayRefs, coming from incoming parameters */
		for (int i = startArgIdx; i < nfParams; ++i) {
			FormalParam fparam = rudce.getFormalParam(i);
			Variable fpvar = makeVariable(fparam.getV(), fparam.getIdStmt()); //new StdVariable(fparam.getV());
			defSet.add(new SVTNode(fpvar, m, fparam.getIdStmt()));
			
			if (fparam.getV().getType() instanceof RefLikeType) {
				localAliasSets.put(fparam.getV(), new LinkedHashSet<SVTNode>());
				localAliasSets.get(fparam.getV()).add(new SVTNode(fpvar, m, fparam.getIdStmt()));
				
				refParams.put(new SVTNode(fpvar, m, fparam.getIdStmt()), i);
			}
		}
		/* defs, including FieldRefs and ArrayRefs, coming from static/instance variable and array element writers */
		defSet.addAll(preDefSet);
		for (Value v : preLocalAliasSets.keySet()) {
			localAliasSets.put(v, new LinkedHashSet<SVTNode>());
			Iterator< SVTNode> iter = preLocalAliasSets.get(v).iterator();
			assert iter.hasNext(); // the initial alias set should always has exactly one element, namely the allocation site itself
			SVTNode aliasSource = iter.next();
			if (aliasSource.getMethod().equals(cfg.getMethod())) {
				localAliasSets.get(v).add( aliasSource );
			}
			assert !iter.hasNext();
		}
		/* Risky operation - will iteratively augment the alias set for each allocation site wronly */
		// localAliasSets.putAll(preLocalAliasSets);
		
		/* now go through all allocation sites and assignment statements 
		 * and create intraprocedrual value transfer edges
		 */
		List<CFGNode> _nodes = cfg.getNodes();
		/* pure intraprocedural definitions of incoming parameters passed by "reference" rather than by "value" */
		List<SVTNode> localDefSet = new LinkedList<SVTNode>();
				
		for (CFGNode _node : _nodes) {
			if (_node.isSpecial()) {
				// skip special, Entry and Exit, nodes
				continue;
			}
			if (dua.Options.ignoreCatchBlocks && _node.isInCatchBlock()) {
				// skip catch blocks and finally blocks
				continue;
			}

			// ONLY FOR TEST: if P2 set in catch blocks got correctly calculated
			/*
			if (_node.isInCatchBlock()) {
				System.out.println("Got a Node in catch/finally block: " + _node);
				if (_node.getStmt() instanceof DefinitionStmt) {
					Value valLhs = ((DefinitionStmt)_node.getStmt()).getLeftOp();
					System.out.println("lhs value type of " + _node + " :" + valLhs.getType());
					if (valLhs.getType() instanceof RefLikeType) {
							System.out.println(P2Analysis.inst().getP2Set(valLhs));
					}
				}
			}
			*/
			
			NodeDefUses node = (NodeDefUses)_node;
			Stmt _s = node.getStmt();
			/** We also connect the defs of each formal parameter at a call site to the Use of that parameter */
			CallSite ncs = node.getCallSite();
			if (ncs != null && ncs.hasAppCallees()) {
				createLocalEdgesForCallSite(defSet, m, ncs, node);
			}
			/* intraprocedural value transfers should be reflected by assignment only when considering the localAliasSet*/
			/*
			if ( !(_s instanceof AssignStmt) ) {
				continue;
			}
			*/
			if ( _s instanceof IdentityStmt) {
				// information needed from ID stmts has been collected in defSet and localAliasSet
				continue;
			}
			if ( _s instanceof ReturnStmt ) {
				createLocalEdgesForReturnStmt(defSet, m, (ReturnStmt)_s, node);
			}
			if ( _s instanceof AssignStmt)  {
				AssignStmt s = (AssignStmt)_s;
				Value lv = s.getLeftOp(), rv = s.getRightOp();
				if (rv instanceof AnyNewExpr/*rv instanceof NewExpr || rv instanceof NewArrayExpr*/) {
					/* object allocation site, including the allocation for a class instance and an array */
					//AllocSite as = new AllocSite(node, rv);
					AnyNewExpr as = (AnyNewExpr)rv;
					assert !localAliasSets.containsKey(as);
	
					/* the first pointer pointing to this allocation site */
					assert lv.getType() instanceof RefLikeType;
					/** use StdVariable instead of ObjVariable to facilitate the graph connectivity modeling*/
					//SVTNode pas = new SVTNode( new ObjVariable(lv, node), m, s);
					SVTNode pas = new SVTNode( makeVariable(lv, s)/*new StdVariable(lv)*/, m, s);
					localAliasSets.put(as, new LinkedHashSet<SVTNode>());
					localAliasSets.get(as).add (pas);
					
					/* update the definition set by adding current def */
					defSet.add(new SVTNode(makeVariable(lv, s)/*new StdVariable(lv)*/,m,s));
					continue;
				}
	
				/*
				 * Constants and Exprs won't contribute to alias classification, and
				 * 	For Refs (ArrayRef or FieldRef), Array Refs are abstracted as Arrays and FieldRefs are
				 * 	handled separately by "instance transfer edges"
				*/
				if (lv.getType() instanceof RefLikeType && lv instanceof Local) {
					/*
					if (!(rv instanceof Local || rv instanceof Ref)) {
						continue;
					}
					if (rv.getType() instanceof NullType) {
						// an initialization to "null" is not a useful assignment for alias classification here
						continue;
					}
					*/
					/* heap object type, including object reference type (RefType) and array type (ArrayType) */
					assert rv.getType() instanceof RefLikeType;
					Set<SVTNode> aliasSet = getAliasSet(localAliasSets, rv);
	 				//assert aliasSet != null && !aliasSet.isEmpty();
					if ( aliasSet != null && !aliasSet.isEmpty() ) {
						/** use StdVariable instead of ObjVariable to facilitate the graph connectivity modeling*/
						//aliasSet.add(new SVTNode( new ObjVariable(lv, node), m, s));
						aliasSet.add(new SVTNode( makeVariable(lv, s)/*new StdVariable(lv)*/, m, s));
						
						/* update the definition set by adding current def */
						defSet.add(new SVTNode( makeVariable(lv, s)/*new StdVariable(lv)*/,m,s));
						continue;
					}
				}
			}
			
			/* Local, array element (ArrayRef) or object field (FieldRef) */
			List<Variable> defs = node.getDefinedVars();
			/*
			for (Variable def : defs) {
				if (def.isLibCallObj()) {
					// Library objects would not involve value transfers we care about	
					defs.remove(def);
				}
			}
			*/
			// for debug: is it possible that there isn't exactly one value defined in an assignment statement??
			// -- Yes, there might be library objects such as String...
			//assert defs.size()==1;
			for (Variable def : defs) {
				Variable defVar = varAbstraction(def, m);
				/* update the local definition set by adding current def */
				localDefSet.add(new SVTNode(defVar,m,_s));

				List<Variable> uses = node.getUsedVars();
				/*
				List<Use> uses4def = DependenceFinder.getAllUsesForDef(def, node);
				List<Variable> usevars4def = new LinkedList<Variable>();
				for (Use use : uses4def) {
					usevars4def.add(use.getVar());
				}
				*/
				for (Variable use : uses) {
					/*
					if (!usevars4def.contains(use)) {
						System.out.println("spurious dua skipped: " + def + "->" + use);
						continue;
					}
					*/
					/* a candidate transfer edge exists between each def->use pair, but
					 * such an edge will be created only if the variable used here was previously defined and collected
					 * in D
					if (use.getValue() instanceof ArrayRef) {
						assert use.getBaseLocal() == uses.get(1).getValue();
					}
					 */
					/** get all defs of use besides those in formal parameters and static/instance variable writers */
					/*
					Set<SVTNode> allDefs = new LinkedHashSet<SVTNode>();
					List<Pair<Def,Integer>> defs4use = DependenceFinder.getAllDefsForUse(use, node);
					for (Pair<Def,Integer> pair : defs4use) {
						if (ProgramFlowGraph.inst().getContainingMethod(pair.first().getN()).equals(m)) {
							//System.out.println("def for use " + use.getValue() + " : " + pair.first().getN().getStmt());
							Def d = pair.first();
							Variable v = d.getVar();
							if (v.getValue() instanceof FieldRef || v.getValue() instanceof ArrayRef) {
								if (v.mayEqualAndAlias(use)) allDefs.add( new SVTNode(varAbstraction(v,m), m, d.getN().getStmt()) );
							}
							else {
								if (v.equals(use)) allDefs.add( new SVTNode(varAbstraction(v,m), m, d.getN().getStmt()) );
							}
						}
					}
					*/
					/** limited to Locals */
					/*
					SimpleLocalDefs defFinder = new SimpleLocalDefs (new ExceptionalUnitGraph(m.getActiveBody()));
					List<Unit> localDefs = defFinder.getDefsOfAt((Local)use.getValue(), s);
					*/
					
					//Variable useVar = varAbstraction(use, m);
					/** it is not correct to pick the recent def among those that are collected in sequence in the jimple body */
					/*
					SVTNode rd = getRecentDef(defSet, useVar);
					if (null == rd) {
						// no value transfer occurs from this use to the current def
						continue;
					}

					//createTransferEdge(def, m, s, rd.getVar(), rd.getMethod(), rd.getStmt(), SVTEdge.VTEType.VTE_INTRA);
					if (rd.getVar() == defVar) {
						// avoid self-edges for now
						continue;
					}
					*/
					/** TODO: compute reachability of defs found in defSet to useVar */
					//allDefs.addAll(getAllDefs(defSet, useVar));
					
					Set<SVTNode> allDefs = getAllDefs(defSet, use, m, node);
					if ((use.isFieldRef() || use.isArrayRef()) && this.getRecentDef(preDefSet, use)!=null) {
						// field refs and array elements will have global RW transfers edges to connect, but a potential writer only connects to 
						// this use itself, no way to further connect to the defVar here now; So such use->def edges are necessary for bridging
						allDefs.add(new SVTNode(use, m, _s));
					}
					
					for (SVTNode rd : allDefs) {
						/** interprocedural transfer edges between FieldRefs and ArrayRefs have been created as Instance/Static var transfer edges
						 * and array element transfer edges respectively, so we avoid repeating them by creating intraprocedural ones here ONLY
						 */
						if ( (use.isArrayRef() && rd.getVar().isArrayRef())  || (use.isFieldRef() && rd.getVar().isFieldRef()) ) {
							// As such, transfers between library objects will be created interprocedurally too!  
							if (!m.equals(rd.getMethod())) {
								continue;
							}
						}
						
						// to avoid the notoriously expensive separate computation of library object RW transfers, we do it there
						boolean interprocLibObjEdge = !m.equals(rd.getMethod()) && use.isObject() && rd.getVar().isObject();
						if (!interprocLibObjEdge) assert m.equals(rd.getMethod()); 
						
						// For a flow-insensitive analysis, create a Local transfer edge from each of the defs of useVar to it
						createTransferEdge(rd.getVar(), rd.getMethod(), rd.getStmt(), 
								defVar, m, _s, interprocLibObjEdge?VTEType.VTE_LIBOBJ : VTEType.VTE_INTRA);
					}
				}
				
				/** we already compute All intraprocedural defs for the each use concerned above, thus no need to collect all defs per
				 * each assignment statement any more - defSet will just be the set of defs found in static and instance variable writers and
				 * formal parameters 
				 */
				/*
				// update the definition set by adding current def
				defSet.add(new SVTNode(defVar,m,s));
				*/
				
			} // for each def in the current node
		} // for each cfg node
		
		/* create transfer edges between alias nodes in each alias class */
		for (Value v:localAliasSets.keySet()) {
			Set<SVTNode> aliasSet = localAliasSets.get(v);
			if (aliasSet.size() < 2) {
				continue;
			}
			
			/* complete graph among nodes in an alias class */
			for (SVTNode src : aliasSet) {
				for (SVTNode tgt : aliasSet) {
					if (src == tgt) {
						continue;
					}
					createTransferEdge(src.getVar(), src.getMethod(), src.getStmt(),
							tgt.getVar(), tgt.getMethod(), tgt.getStmt(), VTEType.VTE_ALIAS);
					/*
					createTransferEdge(tgt.getVar(), tgt.getMethod(), tgt.getStmt(),
							src.getVar(), src.getMethod(), src.getStmt(), SVTEdge.VTEType.VTE_ALIAS);
					*/		
				}
			}
		} // for each alias class
		
		/* create reference parameter return edges if the parameter is changed in m as a callee */
		/** However, usually such reference parameters should be heap objects like object fields and array elements;
		 *  And, we have already connect the writers to readers of those heap objects separately. So this step becomes redundant;
		 *  Further, if we don't further check if the caller, after receiving the change made in the callee, really uses these parameters,
		 *  it would be imprecise to create these transfer edges. Fact is, it is not cheap to check this. 
		 *  
		 *  So, we could skip creating such type of transfer edges, for both performance and precision!
		 */
		 createRefParamRetTransferEdges(cfg, localDefSet, refParams, localAliasSets);
		
	} // createIntraproceduralValueTransferEdges
		
	/** create transfer edges between reference formal parameter and actual parameter if the formal
	 * parameter is redefined directly or via alias 
	 */
	protected void createRefParamRetTransferEdges(CFG cfg, List<SVTNode> localDefSet, 
			Map<SVTNode, Integer> refParams, Map<Value, Set<SVTNode>> localAliasSets) {
		ReachableUsesDefs rudce = (ReachableUsesDefs) cfg;
		for (SVTNode fparam : refParams.keySet()) {
			Set<SVTNode> fparamAliasSet = null;
			for (Value v:localAliasSets.keySet()) {
				if (localAliasSets.get(v).contains(fparam)) {
					fparamAliasSet = localAliasSets.get(v); 
					break;
				}
			}
			/* any refTypeLike parameter should have its alias set already */
			assert fparamAliasSet != null;
			
			/* if any node in the alias set of fparam has ever been defined, we create a reference parameter
			 * back edge from callee to caller for it since this "definition" will propagate this change back to the
			 * caller; 
			 * Note: again, we assume there will be at least one use after each definition, even though this
			 * def-use is across caller and callee;
			 * namely,  for this kind of edges as is treated here, we assume the parameter will be used again
			 * after the call site in the caller
			 */
			boolean changed = false;
			SVTNode reDef = null;
			for (SVTNode n : fparamAliasSet) {
				//if (localDefSet.contains(n)) {
				if( (reDef=getRecentDef(localDefSet, n.getVar())) != null) {
					/* as long as there has been a change to any node in the alias set of fparam, we know fparam
					 * has been changed directly or indirectly
					 */
					changed = true;
					break;
				}
			}
			if (!changed) {
				// create back edges only for reference parameters that have been changed
				continue;
			}
			
			/* we need connect a changed reference parameter from callee to each possible caller site */
			int paramIdx = refParams.get(fparam);
			for (CallSite callersite : cfg.getCallerSites()) {
				for (SootMethod callee : callersite.getAppCallees()) {
					if (!callee.equals(cfg.getMethod())) {
						// connect caller to the right callee
						continue;
					}
					Stmt sIdFormal = rudce.getFormalParam(paramIdx).getIdStmt();
					Value aval = callersite.getActualParam(paramIdx);
					/** use StdVariable instead of CSArgVar to facilitate the graph connectivity modeling*/
					//Variable avar = new CSArgVar(aval, callersite, paramIdx);
					Variable avar = makeVariable(aval, callersite.getLoc().getStmt());//new StdVariable(aval);
					Value fval = rudce.getFormalParam(paramIdx).getV();
					//Variable fvar = new CSArgVar(fval, callersite, paramIdx); // here callersite serves a place-holder only
					Variable fvar = makeVariable(fval, sIdFormal);//new StdVariable(fval);
					
					// connect from the Redefinition site of the refparam back to the caller site
					createTransferEdge( /*varAbstraction(fvar,callee), callee, sIdFormal,*/
							reDef.getVar(), reDef.getMethod(), reDef.getStmt(),
							varAbstraction(avar,callersite.getLoc().getMethod()), callersite.getLoc().getMethod(), callersite.getLoc().getStmt(),
							VTEType.VTE_PARARET);
					
					// also, now the caller site becomes an extra definition site of the refparam, so connect from the caller site to its def sites
					// of the refparam
					CFGNode clrn = ProgramFlowGraph.inst().getNode(callersite.getLoc().getStmt());
					Set<SVTNode> defs4avar = getAllDefs(new ArrayList<SVTNode>(), avar, callersite.getLoc().getMethod(), clrn);
					for (SVTNode d : defs4avar) {
						createTransferEdge(
								varAbstraction(avar,callersite.getLoc().getMethod()), callersite.getLoc().getMethod(), callersite.getLoc().getStmt(),
								d.getVar(), d.getMethod(), d.getStmt(), VTEType.VTE_PARARET);
						// since in the caller site all defs of avar are connected to any other def/call site that uses it, we need connect only to one
						break;
					}
				}
			}
		} // for each reference parameter
	}
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	 /**
     * Save the state of the <tt>StaticTransferGraph</tt> instance to a stream (i.e.,
     * serialize it).
     *
     * @serialData list of all nodes followed by the edges denoted by node index to the node list
     */
    private void writeObject(java.io.ObjectOutputStream s)
        throws IOException
    {
        // Write out any hidden stuff
        s.defaultWriteObject();

        /* Write all nodes : since we only have the class of Variable, namely StdVariable, for all SVTNodes, we simply
         * serialize the underlying Soot.Value for the internal Variables;
         * 
         *  For the internal SootMethod, which is not serializable, we serialize its name, parameter type list and return type;
         *  For the internal Stmt, we serialize it as an object since it is serializable already
         */
        // Write the size of node list
        s.writeInt(nodes.size());
        for (SVTNode node : nodes) {
        	/** Write the Variable, only the Value inside - all using a phantom Local to represent due to the complexity of serializing
        	 *   FieldRef and ArrayRef 
        	 */
        	//s.writeObject(node.getVar().getValue());
        	s.writeObject(utils.getCanonicalFieldName(node.getVar()));
        	//s.writeObject(node.getVar().getValue().getType());
        	s.writeObject(IntConstant.v(0).getType()); // dummy stuffing
        	
        	// Write the SootMethod, only its name, parameter type list and return type
        	s.writeObject(node.getMethod().getDeclaringClass().getName());
        	//s.writeObject(node.getMethod().getName());
        	s.writeObject(node.getMethod().getSignature());
        	s.writeInt(node.getMethod().getParameterCount());
        	for (Type t : (List<Type>)node.getMethod().getParameterTypes()) {
        		//s.writeObject(t);
        		s.writeObject(IntConstant.v(0).getType()); // dummy stuffing
        	}
        	//s.writeObject(node.getMethod().getReturnType());
        	s.writeObject(IntConstant.v(0).getType()); // dummy stuffing
        	/** Write the Stmt as an object - unfortunately, some Stmt can not be serialized if it contains unserializable internal object
        	 *  we use a Constant Value to hold the stmt id only, and then create an ReturnStmt to embody the Value 
        	 */
        	int sid = -1; // -1 indicates "unknown" statement id
        	try { sid = StmtMapper.getGlobalStmtId(node.getStmt()); } catch(Exception e) {}
        	s.writeObject( Jimple.v().newReturnStmt( IntConstant.v(sid) ) ); 
        	//s.writeObject((Stmt)node.getStmt());
        }
         
        // indexing nodes for edges
        Map<SVTNode, Integer> nodeToIdx = new LinkedHashMap<SVTNode, Integer>();
        int idx = 0;
        for (SVTNode node : nodes) {
        	nodeToIdx.put(node, idx++);
        }
        
        // Write all edges using src and tgt node indices
        s.writeInt(edges.size());
        for (SVTEdge e : edges) {
        	s.writeInt( nodeToIdx.get(e.getSource()) );
        	s.writeInt( nodeToIdx.get(e.getTarget()) );
        	//s.writeByte(e.getEdgeType().ordinal() - SVTEdge.VTEType.VTE_UNKNOWN.ordinal());
        	s.writeObject(e.getEdgeType());
        }
        // -
        s.flush();
    }

    private static final long serialVersionUID = 0x438200DE;
    /**
     * Reconstitute the <tt>StaticTransferGraph</tt> instance from a stream (i.e.,
     * deserialize it).
     */
    private void readObject(java.io.ObjectInputStream s)
         throws IOException, ClassNotFoundException
    {
        // Read any hidden stuff
        s.defaultReadObject();
        
        // create internal memory blocks
        /*
		nodes = new LinkedHashSet<SVTNode>();
		edges = new LinkedHashSet<SVTEdge>();
		nodeToEdges = new LinkedHashMap< SVTNode, Set<SVTEdge> >();
		reachableMethods = null;
		*/
        initInternals();

        // Load the node list
        int szNodelist = s.readInt();
        List<SVTNode> nodelist = new ArrayList<SVTNode>(szNodelist);
        Map<String, SootMethod> name2me = new LinkedHashMap<String, SootMethod>(); // cache the faked dummy methods
        for (int i = 0; i < szNodelist; ++i) {
        	// Read the value underlying the variable for the current node
        	//Variable var = new StdVariable( (Value)s.readObject() );
        	Variable var = new StdVariable( Jimple.v().newLocal((String)s.readObject(), (Type)s.readObject()) );
        	
        	// Read the SootMethod
        	// First the name of the method written as bytes before
        	String cname = (String) s.readObject();
        	String sname = (String) s.readObject();
        	List<Type> ptlist = new LinkedList<Type>();
        	int szParamlist = s.readInt();
        	// Read the list of parameter types
        	for (int j = 0; j < szParamlist; ++j) {
        		ptlist.add((Type)s.readObject());
        	}
        	// Read the return type and instantiate a SootMethod object
        	Type rtype = (Type)s.readObject();
        	SootMethod me = name2me.get(cname+"::"+sname);
        	if (null == me) {
	        	me = new SootMethod(sname, ptlist, rtype, Modifier.PUBLIC | Modifier.STATIC);
	        	Body by = Jimple.v().newBody();
	        	SootClass cls = new SootClass(cname);
	        	me.setDeclared(true); 
	        	me.setDeclaringClass(cls);
	        	by.setMethod(me);
	        	me.setActiveBody(by);
	        	name2me.put(cname+"::"+sname, me);
        	}
        	
        	// Read the Stmt and instantiate a SVTNode object
        	Stmt stmt = (Stmt)s.readObject();
        	SVTNode node = new SVTNode(var, me, stmt);
        	
        	nodelist.add(i, node);
        }
        
        // Load the edge list and build the VTG itself
        int szEdgelist = s.readInt();
        for (int k = 0; k < szEdgelist; ++k) {
        	// Read the src and tgt node indices
        	int src = s.readInt();
        	int tgt = s.readInt();
        	VTEType et = (VTEType)s.readObject();
        	// Read the edge type and instantiate an edge object then add it to the graph
        	createTransferEdge( nodelist.get(src), nodelist.get(tgt), et, false );
        }
        // - 
    }
	
	public StaticTransferGraph DeserializeFromFile(String sfn) {
		Object o = super.DeserializeFromFile(sfn);
		if (o != null) {
			StaticTransferGraph vtg = new StaticTransferGraph();
			vtg = (StaticTransferGraph)o;
			this.CopyFrom(vtg);
			return vtg;
		}
			
		return null;
	} // DeserializeFromFile
	
	/**
	 * for debugging purposes, list all edge details
	 * @param listByEdgeType
	 * 	@return 0 - already done; 1 - more needed
	 */
	public int dumpGraphInternals(boolean listByEdgeType) {
		if (0 == super.dumpGraphInternals(listByEdgeType)) {
			return 0;
		}
		
		/* list nodes by enclosing methods */
		Map<SootMethod, List<SVTNode>> method2nodes = new LinkedHashMap<SootMethod, List<SVTNode>>();
		for (SVTNode vn : nodes) {
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
		
		/* list edges by types */
		Map<VTEType, List<SVTEdge>> type2edges = new LinkedHashMap<VTEType, List<SVTEdge>>();
		for (SVTEdge edge : edges) {
			List<SVTEdge> els = type2edges.get(edge.getEdgeType());
			if (els == null) {
				els = new LinkedList<SVTEdge>();
				type2edges.put(edge.getEdgeType(), els);
			}
			els.add(edge);
		}
		for (Map.Entry<VTEType, List<SVTEdge>> en : type2edges.entrySet()) {
			System.out.println("----------------------------------------- " + 
					VTEdge.edgeTypeLiteral(en.getKey()) + " [" +	en.getValue().size() + 
					" edges] -----------------------------------------");
			for (SVTEdge edge : en.getValue()) {
				System.out.println("\t"+edge);
			}
		}
		
		return 0;
	} // dumpGraphInternals
	
	/** check VTG edges having object variable (including library objects) at either endpoint 
	 * against static forward slice to examine if the static VTG constructed in Diver missed any 
	 * dependences concerning object variables 
	 */
	public void checkObjvarDeps() {
		// check dependents of an objVar SVTNode
		for (CFG cfg : ProgramFlowGraph.inst().getCFGs()) {
			CFG targetcfgObjD = null;
			CFGNode nStartObjD = null;
		
			if (((CFGDefUses)cfg).getLibObjDefs().size() < 1) { continue; }
			
			targetcfgObjD = cfg;
			Def objdef = ((CFGDefUses)cfg).getLibObjDefs().get(0);
			nStartObjD = objdef.getN();
			assert objdef.getVar().isObject();
				
			// there should be at least one CFGNode having libObj defs
			assert targetcfgObjD !=null && nStartObjD != null;
					
			NodePoint startND = new NodePoint(nStartObjD, NodePoint.POST_RHS);
			DependenceGraph dgd = new DependenceGraph(startND, -1);
			Set<SVTNode> vtgNodesStartD = new LinkedHashSet<SVTNode>();
			for (SVTNode sn : this.nodes) {
				if (sn.getStmt().equals(nStartObjD.getStmt())) {
					vtgNodesStartD.add(sn);
				}
			}
			for (Dependence dep : dgd.getOutDeps(startND)) {
				// because usually VTG only connects def to def
				if ( ((NodeDefUses)dep.getTgt().getN()).getDefinedVars().size() < 1) {continue;}
				boolean found = false;
				for (SVTNode sn : vtgNodesStartD) {
					if (null == this.getOutEdges(sn)) { continue; }
					for (SVTEdge se : this.getOutEdges(sn)) {
						if (dep.getTgt().getN().getStmt().equals(se.getTarget().getStmt())) {
							found = true;
							System.out.println("Yes, dependent of the chosen start in fwslice  [" + dep + "] matched in SVTG [" + se + "]");
						}
					}
				}
				if (!found) {
					System.out.println("ERROR, dependent of the chosen start in fwslice  [" + dep + "] NOT matched in SVTG [");
				}
			}
		}
		
		// check dependences of an objVar SVTNode
		for (CFG cfg : ProgramFlowGraph.inst().getCFGs()) {
			CFG targetcfgObjU = null;
			CFGNode nStartObjU = null;
			CFGNode nStartObjUD = null;
			
			List<Use> uses = ((CFGDefUses)cfg).getLibObjUses();
			for (int i = 0; i < uses.size(); i++) {
				targetcfgObjU = cfg;
				Use objuse = uses.get(i);
				assert objuse.getVar().isObject();
				nStartObjU = objuse.getN();
				List<Pair<Def, Integer>> def4use = DependenceFinder.getAllDefsForUse(objuse.getVar(), objuse.getN());
				if (def4use.size() >= 1) {
					nStartObjUD = def4use.get(0).first().getN();
					break;
				}
			}
			if (null == nStartObjUD) { continue; }
			// there should be at least one CFGNode having libObj uses
			assert targetcfgObjU !=null && nStartObjU != null;
			
			NodePoint startNU = new NodePoint(nStartObjU, NodePoint.POST_RHS);
			NodePoint startNUD = new NodePoint(nStartObjUD, NodePoint.POST_RHS);
			DependenceGraph dgu = new DependenceGraph(startNUD, -1);
			Set<SVTNode> vtgNodesStartU = new LinkedHashSet<SVTNode>();
			for (SVTNode sn : this.nodes) {
				if (sn.getStmt().equals(nStartObjU.getStmt())) {
					vtgNodesStartU.add(sn);
				}
			}
			for (Dependence dep : dgu.getDeps()) {
				if (!dep.getTgt().equals(startNU)) { continue; }
				// because usually VTG only connects def to def
				if ( ((NodeDefUses)dep.getTgt().getN()).getDefinedVars().size() < 1) {continue;}
				boolean found = false;
				for (SVTNode sn : vtgNodesStartU) {
					for (SVTEdge se : this.edges) {
						if (!se.getTarget().equals(sn)) {continue;}
						if (dep.getSrc().getN().getStmt().equals(se.getSource().getStmt())) {
							found = true;
							System.out.println("Yes, dependence of the chosen start in fwslice  [" + dep + "] matched in SVTG [" + se + "]");
						}
					}
				}
				if (!found) {
					System.out.println("ERROR, dependence of the chosen start in fwslice  [" + dep + "] NOT matched in SVTG [");
				}
			}
		}
	}
	
} // definition of StaticTransferGraph

/* vim :set ts=4 tw=4 tws=4 */
