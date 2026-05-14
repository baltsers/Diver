/**
 * File: src/MciaUtil/SVTG.java
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
 *  
*/
package MciaUtil;

import java.io.*;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import dua.global.ProgramFlowGraph;
import dua.global.dep.DependenceFinder;
import dua.global.p2.P2Analysis.AllocSite;
import dua.method.CFG;
import dua.method.CFGDefUses;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.CSReturnedVar;
import dua.method.CFGDefUses.NodeDefUses;
import dua.method.CFGDefUses.ReturnVar;
import dua.method.CFGDefUses.StdVariable;
import dua.method.CFGDefUses.ObjVariable;
import dua.method.ReachableUsesDefs;
import dua.method.CFGDefUses.CSArgVar;
import dua.method.CFGDefUses.Def;
import dua.method.CFGDefUses.Use;
import dua.method.CFGDefUses.Variable;
import dua.method.CallSite;
import dua.method.ReachableUsesDefs.FormalParam;
import fault.StmtMapper;

import soot.*;
import soot.jimple.*;
import soot.util.*;

import MciaUtil.*;

/** the static value transfer graph (VTG) that models value flow relations between variables, 
 * both intra- and inter-procedurally;
 *
 * VTG serves tracing value flow of variables that potentially propagates the impacts of original changes
 */
final class SVTG implements Serializable {
	/** A static VTG node describes basic info about a variable w.r.t its service for value flow 
	 * tracing of the variable 
	 */
	public static class SVTNode {
		/** variable underneath */
		protected final Variable v;
		/** enclosing/hosting method of the variable */
		protected final SootMethod m;
		/** statement location of the node */
		protected Stmt s;
		
		/** we may ignore stmt. loc. for some variables temporarily */
		public SVTNode(Variable _v, SootMethod _m) {
			v = _v;
			m = _m;
			s = null;
		}
		public SVTNode(Variable _v, SootMethod _m, Stmt _s) {
			v = _v;
			m = _m;
			s = _s;
		}
		
		/** accessors */
		void setStmt(Stmt _s) { this.s = _s; }
		public Variable getVar() { return v; }
		public SootMethod getMethod() { return m; }
		public Stmt getStmt() { return s; }
		
		@Override public int hashCode() {
			/* NOTE: different types of variable can be assigned different hash code even though the underlying value is the same */
			//return (m.hashCode() & 0xffff0000) | (v.hashCode() & 0x0000ffff);
			return (m.hashCode() & 0xffff0000) | (v.getValue().hashCode() & 0x0000ffff);
		}
		/** we do not distinguish two VTG nodes by statement location only */
		@Override public boolean equals(Object o) {
			//return v.mayEqualAndAlias(((SVTNode)o).v) && m == ((SVTNode)o).m;
			//return v == ((SVTNode)o).v && m == ((SVTNode)o).m;
			//return dua.util.Util.valuesEqual(v.getValue(), ((SVTNode)o).v.getValue(), true) && m == ((SVTNode)o).m;
			
			//return v.equals( ((SVTNode)o).v ) && m.equals( ((SVTNode)o).m );
			try {
				return v.mayEqualAndAlias(((SVTNode)o).v) && m.equals( ((SVTNode)o).m );
			}
			catch (Exception e) {
				/** this is for the makeshift during Serialization of the "SootMethod" field of SVTNode ONLY */
				return utils.getCanonicalFieldName(v).equalsIgnoreCase(utils.getCanonicalFieldName (((SVTNode)o).v)) &&
							m.getName().equalsIgnoreCase( ((SVTNode)o).m.getName());
			}
		}
		/* exactly equal comparator */
		public boolean strictEquals(Object o) {
			//return this == o && s == ((SVTNode)o).s;
			return this.equals(o) && s.equals( ((SVTNode)o).s );
		}
		public String toStringNoStmt() {
			return "("+utils.getCanonicalFieldName(v)+","+m.getName()+")";
		}
		@Override public String toString() {
			if (null != s) {
				String sid = "";
				try {
					sid += StmtMapper.getGlobalStmtId(s);
				}
				catch(Exception e) {
					if (s instanceof ReturnStmt && ((ReturnStmt)s).getOp() instanceof IntConstant) {
						/** this is for the makeshift during Serialization of the "Stmt" field of SVTNode ONLY */
						sid += ( (IntConstant) ((ReturnStmt)s).getOp() ).toString();
					}
					else {
						sid = "unknown";
					}
				}
				return "("+utils.getCanonicalFieldName(v)+","+m.getDeclaringClass().getName()+"::"+m.getName()+","+sid+")";
			}
			return "("+utils.getCanonicalFieldName(v)+","+m.getDeclaringClass().getName()+"::"+m.getName()+")";
		}

		public static class SVTNodeComparator implements Comparator<SVTNode> {
			private SVTNodeComparator() {}
			public static final SVTNodeComparator inst = new SVTNodeComparator();

			public int compare(SVTNode n1, SVTNode n2) {
				final String mname1 = n1.m.getName();
				final String mname2 = n2.m.getName();

				final String vname1 = n1.v.toString();
				final String vname2 = n2.v.toString();

				int cmpmName = mname1.compareToIgnoreCase(mname2);
				int cmpvName = vname1.compareToIgnoreCase(vname2);
				if (null == n1.s || null == n2.s) {
					return (cmpmName != 0)?cmpmName : cmpvName; 
				}

				final int sid1 = StmtMapper.getGlobalStmtId(n1.s);
				final int sid2 = StmtMapper.getGlobalStmtId(n2.s);
				return (cmpmName != 0)?cmpmName : (cmpvName != 0)?cmpvName:
					(sid1 > sid2)?1:(sid1 < sid2)?-1:0;
			}
		}
	}

	/** A static VTG edge as a component of VTG models the value flow relation from a writer (source)
	 * to a reader (target) of a variable
	 */
	public static class SVTEdge {
		/** possible value transfer edge types */
		public static enum VTEType { VTE_UNKNOWN, VTE_STVAR, VTE_INSVAR, 
			VTE_PARAM, VTE_RET, VTE_PARARET, VTE_INTRA, VTE_ALIAS, VTE_ARRAYELE };

		protected final SVTNode src;
		protected final SVTNode tgt;
		protected final VTEType etype;

		/** accessors */
		public SVTNode getSource() { return src; }
		public SVTNode getTarget() { return tgt; }
		public VTEType getEdgeType() { return etype; }
		/** determinants */
		boolean isParameterEdge() { return VTEType.VTE_PARAM == etype; }
		boolean isStaticVarEdge() { return VTEType.VTE_STVAR == etype; }
		boolean isInstanceVarEdge() { return VTEType.VTE_INSVAR == etype; }
		boolean isReturnEdge() { return VTEType.VTE_RET == etype; }
		boolean isRefReturnParamEdge() { return VTEType.VTE_PARARET == etype; }
		boolean isIntraEdge() { return VTEType.VTE_INTRA == etype; }
		boolean isAliasEdge() { return VTEType.VTE_ALIAS == etype; }
		boolean isArrayEleEdge() { return VTEType.VTE_ARRAYELE == etype; }

		public SVTEdge(SVTNode _src, SVTNode _tgt, VTEType _etype) { 
			src = _src; 
			tgt = _tgt;
			etype = _etype;
		}

		static	final String[] typeLiterals = new String[] {
			"unknown", "staticVariableEdge", "instanceVariableEdge", "parameterEdge",
				"returnEdge", "refParamReturnEdge", "intraproceduralEdge", "aliasEdge", "arrayEleEdge"};
		static String edgeTypeLiteral(VTEType _etype) {
			return typeLiterals[_etype.ordinal() - VTEType.VTE_UNKNOWN.ordinal()];
		}

		@Override public int hashCode() {
			return (src.hashCode() & 0xffff0000) | (tgt.hashCode() & 0x0000ffff);  
		}
		/** we do not distinguish two VTG nodes by statement location only */
		@Override public boolean equals(Object o) {
			/* After long peeve debugging, taught that the equal operator "==" should never be readily used with non-primitives */ 
			/*
			return src == ((SVTEdge)o).src && tgt == ((SVTEdge)o).tgt 
				&& etype == ((SVTEdge)o).etype;
				*/
			return src.equals(((SVTEdge)o).src) && tgt.equals( ((SVTEdge)o).tgt ) 
					&& etype == ((SVTEdge)o).etype;
		}
		/** exactly equal comparator */
		public boolean strictEquals(Object o) {
			return src.strictEquals(((SVTEdge)o).src) && tgt.strictEquals(((SVTEdge)o).tgt) 
				&& etype == ((SVTEdge)o).etype;
		}
		public String toString(boolean withStmt, boolean withType) {
			String ret = "<";
			ret += (withStmt)?src : src.toStringNoStmt();
			ret += ",";
			ret += (withStmt)?tgt : tgt.toStringNoStmt();
			ret += ">";
			if (withType) {
				ret += ":" + edgeTypeLiteral(etype);
			}
			return ret;
		}
		@Override public String toString() {
			return toString(true, true);
		}

		public static class SVTEdgeComparator implements Comparator<SVTEdge> {
			private final Map<SVTEdge, Integer> edgeIds;
			public SVTEdgeComparator(Map<SVTEdge, Integer> _edgeIds) { edgeIds = _edgeIds; }

			public int compare(SVTEdge e1, SVTEdge e2) {
				final int eid1 = edgeIds.get(e1);
				final int eid2 = edgeIds.get(e2);

				return (eid1 > eid2)?1:(eid1 < eid2)?-1:0;
			}
		}
	}

	/** data members of a Value Transfer Graph */
	/** all nodes */
	transient Set<SVTNode> nodes; 
	/** all edges */
	transient Set<SVTEdge> edges;
	/** map from a node to all outgoing edges */
	transient Map< SVTNode, Set<SVTEdge> > nodeToEdges;
	
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
	
	/* all reachable application methods - retrieve in advance for efficient later accesses */
	transient static List<SootMethod> reachableMethods;

	private void initInternals() {
		nodes = new LinkedHashSet<SVTNode>();
		edges = new LinkedHashSet<SVTEdge>();
		nodeToEdges = new LinkedHashMap< SVTNode, Set<SVTEdge> >();
		reachableMethods = null;
	}
	public SVTG() {
		initInternals();
	}
	
	@Override public String toString() {
		return "Value Transfer Graph: " + nodes.size() + " nodes, " + edges.size() + " edges ";
	}
	
	/** accessors */
	public Set<SVTNode> nodeSet() { return nodes; }
	public Set<SVTEdge> edgeSet() { return edges; }
	public Set<SVTEdge> getOutEdges(SVTNode _node) { return nodeToEdges.get(_node); }
	
	/** a convenient routine for adding an edge and the covered nodes into the graph */
	/** a convenient routine for adding an edge and the covered nodes into the graph */
	private void createTransferEdge(Variable srcVar, SootMethod srcMethod, Stmt srcStmt,
															Variable tgtVar, SootMethod tgtMethod, Stmt tgtStmt, 
															SVTEdge.VTEType etype) {
		createTransferEdge(srcVar, srcMethod, srcStmt, tgtVar, tgtMethod, tgtStmt, etype, true);
	}
	private void createTransferEdge(Variable srcVar, SootMethod srcMethod, Stmt srcStmt,
															Variable tgtVar, SootMethod tgtMethod, Stmt tgtStmt, 
															SVTEdge.VTEType etype, boolean reachabilityCheck) {
		if (reachabilityCheck) {
			// any transfer edges associated with methods unreachable from entry should be ignored
			if ( !(reachableMethods.contains(srcMethod) && reachableMethods.contains(tgtMethod) ) ) {
				return;
			}
		}
		SVTNode src = new SVTNode(srcVar, srcMethod, srcStmt);
		SVTNode tgt = new SVTNode(tgtVar, tgtMethod, tgtStmt);
		SVTEdge edge = new SVTEdge(src, tgt, etype);
		
		nodes.add(src);
		nodes.add(tgt);
		edges.add(edge);
		
		Set<SVTEdge> outEdges = nodeToEdges.get(src);
		if (null == outEdges) {
			outEdges = new HashSet<SVTEdge>();
		}
		outEdges.add(edge);
		nodeToEdges.put(src, outEdges);
	}
	
	private void createTransferEdge(SVTNode src, SVTNode tgt, SVTEdge.VTEType etype, boolean reachabilityCheck) {
		createTransferEdge(src.getVar(), src.getMethod(), src.getStmt(),
											tgt.getVar(), tgt.getMethod(), tgt.getStmt(), etype, reachabilityCheck);
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
				String meId = sClass.getName() +	"::" + sMethod.getName();
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
				 * "final" variables because there are not writable thus not involve in transferring impacts
				 */
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
					
					/* collect static variable writers */
					if (df.isStatic()) {
						Set<methodStmtPair> mspairs = globalWS.get(d.getVar());
						if (null == mspairs) {
							mspairs = new HashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
						globalWS.put(d.getVar(), mspairs);
					}
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
					
					/* collect static variable readers */
					if (uf.isStatic()) {
						Set<methodStmtPair> mspairs = globalRS.get(u.getVar());
						if (null == mspairs) {
							mspairs = new HashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
						globalRS.put(u.getVar(), mspairs);
					}
					else {
						Set<methodStmtPair> mspairs = insvRS.get(u.getVar());
						if (null == mspairs) {
							mspairs = new HashSet<methodStmtPair>();
						}
						mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
						insvRS.put(u.getVar(), mspairs);
					}
				} // for all each field use
				
				/*
				 * collect reader and writer methods of all static and instance variables
				 * "final" variables because there are not writable thus not involve in transferring impacts
				 */
				List<Def> aeDefs = cfgDUs.getArrayElemDefs();
				List<Use> aeUses = cfgDUs.getArrayElemUses();
				for (Def d : aeDefs) {
					assert d.getValue() instanceof ArrayRef; 
					ArrayRef ar = (ArrayRef)d.getValue();

					/* collect array element  writers */
					Set<methodStmtPair> mspairs = arrayEleWS.get(d.getVar());
					if (null == mspairs) {
						mspairs = new HashSet<methodStmtPair>();
					}
					mspairs.add( new methodStmtPair(sMethod, d.getN().getStmt()) );
					arrayEleWS.put(d.getVar(), mspairs);
				}
				
				for (Use u : aeUses) {
					assert u.getValue() instanceof ArrayRef; 
					ArrayRef ar = (ArrayRef)u.getValue();
									
					Set<methodStmtPair> mspairs = arrayEleRS.get(u.getVar());
					if (null == mspairs) {
						mspairs = new HashSet<methodStmtPair>();
					}
					mspairs.add( new methodStmtPair(sMethod, u.getN().getStmt()) );
					arrayEleRS.put(u.getVar(), mspairs);
				} // for all each array element use
				
			} // for each method
		} // for each class
		
		return 0;
	}
	
	/** build the VTG of the classes loaded by Soot for analysis
	 * @param debugOut true for logging internal steps and notices during the graph construction
	 * @return 0 for success, otherwise, exception thrown tells error messages
	 */ 
	public int buildGraph(boolean debugOut) throws Exception {
		reachableMethods = ProgramFlowGraph.inst().getReachableAppMethods();
		/* traverse all classes - the first pass, for computing write and read sets of object fields and array elements */
		computeRWSets(debugOut);
				
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
				String meId = sClass.getName() +	"::" + sMethod.getName();
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
				createIntraproceduralValueTransferEdges(cfg, globalWS, insvWS);
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
						if (mspSrc.method() == mspTgt.method()) {
							/* avoid self-edges for now */
							continue;
						}
						
						createTransferEdge(varAbstraction(v,mspSrc.method()), mspSrc.method(), mspSrc.stmt(), 
								varAbstraction(rv,mspTgt.method()), mspTgt.method(), mspTgt.stmt(), SVTEdge.VTEType.VTE_INSVAR);
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
						if (mspSrc.method() == mspTgt.method()) {
							/* avoid self-edges for now */
							continue;
						}
						
						createTransferEdge(varAbstraction(v,mspSrc.method()), mspSrc.method(), mspSrc.stmt(), 
								varAbstraction(rv,mspTgt.method()), mspTgt.method(), mspTgt.stmt(), SVTEdge.VTEType.VTE_ARRAYELE);
					}
				}
			}
		}
		
		/*
		 * 7. create static variable value transfer edges for the subject as a whole, involving
		 * all possible application classes 
		 */
		for (Variable v:globalWS.keySet()) {
			if (!globalRS.containsKey(v)) {
				/* no paired read-write, no edge */
				continue;
			}
			for (methodStmtPair mspSrc : globalWS.get(v)) {
				for (methodStmtPair mspTgt : globalRS.get(v)) {
					if (mspSrc.method() == mspTgt.method()) {
						/* avoid self-edges for now */
						continue;
					}
					
					createTransferEdge(v, mspSrc.method(), mspSrc.stmt(), 
							v, mspTgt.method(), mspTgt.stmt(), SVTEdge.VTEType.VTE_STVAR);
				}
			}
		}
		return 0;
	}
	
	private void createParameterTransferEdges(CFG cfg) {
		List<CallSite> cses = cfg.getCallerSites();
		for (CallSite cs : cses) {
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
					Variable avar = new StdVariable(aval);
					Value fval = rudce.getFormalParam(i).getV();
					//Variable fvar = new CSArgVar(fval, cs, i); // here cs serves a place-holder only
					Variable fvar = new StdVariable(fval);
					
					//assert cfg.getMethod() != cs.getLoc().getMethod();
					createTransferEdge(avar, cs.getLoc().getMethod(), cs.getLoc().getStmt(), 
							fvar, ce, sIdFormal, SVTEdge.VTEType.VTE_PARAM);
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
			StdVariable csretVar = new StdVariable( ((AssignStmt)sCaller).getLeftOp() );
			
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
				rVar = new StdVariable(retv);
				
				createTransferEdge(rVar, m, s, varAbstraction(csretVar,m), mCaller, sCaller, SVTEdge.VTEType.VTE_RET);
				
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
	/** a helper function, searching the most recent def of a variable, for createIntraproceduralValueTransferEdges */
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
	
	/** a helper function, abstracting a variable into simpler form if it is object field or array element, for 
	 * createIntraproceduralValueTransferEdges;
	 * - for object field, ignore object and just take the field;
	 * - for array element, ignore index/element and just take the array 
	 */
	private Variable varAbstraction(Variable v, SootMethod m) {
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
	private void createIntraproceduralValueTransferEdges(CFG cfg, Map<Variable, 
			Set<methodStmtPair>> globalWS, Map<Variable, Set<methodStmtPair>> insvWS) {
		/* initial definition set */
		List<SVTNode> defSet = new LinkedList<SVTNode>();
		SootMethod m = cfg.getMethod();
		ReachableUsesDefs rudce = (ReachableUsesDefs) ProgramFlowGraph.inst().getCFG(m);
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
		Map<Value, Set<SVTNode>> localAliasSets = new HashMap<Value, Set<SVTNode>>();
		
		/* defs, including references and arrays, coming from incoming parameters */
		for (int i = startArgIdx; i < nfParams; ++i) {
			FormalParam fparam = rudce.getFormalParam(i);
			StdVariable fpvar = new StdVariable(fparam.getV());
			defSet.add(new SVTNode(fpvar, m, fparam.getIdStmt()));
			
			if (fparam.getV().getType() instanceof RefLikeType) {
				localAliasSets.put(fparam.getV(), new HashSet<SVTNode>());
				localAliasSets.get(fparam.getV()).add(new SVTNode(fpvar, m, fparam.getIdStmt()));
				
				refParams.put(new SVTNode(fpvar, m, fparam.getIdStmt()), i);
			}
		}
		/* defs, including references and arrays, coming from static Variables */
		for (Map.Entry<Variable, Set<methodStmtPair>> en : globalWS.entrySet()) {
			methodStmtPair firstPair = null;
			for (methodStmtPair mp : en.getValue()) {
				defSet.add(new SVTNode(en.getKey(), mp.method(), mp.stmt()));
				if (null == firstPair) {
					firstPair = mp;
				}
			}
			
			assert firstPair != null;
			if (en.getKey().getValue().getType() instanceof RefLikeType) {
				localAliasSets.put(en.getKey().getValue(), new HashSet<SVTNode>());
				localAliasSets.get(en.getKey().getValue()).add(
						new SVTNode( new StdVariable(en.getKey().getValue()), firstPair.method(), firstPair.stmt()));
			}
		}
		/* defs, including references and arrays, coming from instance Variables */
		for (Map.Entry<Variable, Set<methodStmtPair>> en : insvWS.entrySet()) {
			methodStmtPair firstPair = null;
			for (methodStmtPair mp : en.getValue()) {
				defSet.add(new SVTNode(en.getKey(), mp.method(), mp.stmt()));
				if (null == firstPair) {
					firstPair = mp;
				}
			}
			
			assert firstPair != null;
			if (en.getKey().getValue().getType() instanceof RefLikeType) {
				localAliasSets.put(en.getKey().getValue(), new HashSet<SVTNode>());
				localAliasSets.get(en.getKey().getValue()).add(
						new SVTNode( new StdVariable(en.getKey().getValue()), firstPair.method(), firstPair.stmt()));
			}
		}
		
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
			NodeDefUses node = (NodeDefUses)_node;
			Stmt _s = node.getStmt();
			if ( !(_s instanceof AssignStmt) ) {
				/* intraprocedural value transfers should be reflected by assignment only */
				continue;
			}
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
				SVTNode pas = new SVTNode( new StdVariable(lv), m, s);
				localAliasSets.put(as, new HashSet<SVTNode>());
				localAliasSets.get(as).add (pas);
				
				/* update the definition set by adding current def */
				defSet.add(new SVTNode(new StdVariable(lv),m,s));
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
					aliasSet.add(new SVTNode( new StdVariable(lv), m, s));
					
					/* update the definition set by adding current def */
					defSet.add(new SVTNode(new StdVariable(lv),m,s));
					continue;
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
				localDefSet.add(new SVTNode(defVar,m,s));

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
					Variable useVar = varAbstraction(use, m); 
					SVTNode rd = getRecentDef(defSet, useVar);
					if (null == rd) {
						/* no value transfer occurs from this use to the current def */
						continue;
					}

					//createTransferEdge(def, m, s, rd.getVar(), rd.getMethod(), rd.getStmt(), SVTEdge.VTEType.VTE_INTRA);
					if (rd.getVar() == defVar) {
						/* avoid self-edges for now */
						continue;
					}
					createTransferEdge(rd.getVar(), rd.getMethod(), rd.getStmt(), 
							defVar, m, s, SVTEdge.VTEType.VTE_INTRA);
				}
				
				/* update the definition set by adding current def */
				defSet.add(new SVTNode(defVar,m,s));
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
							tgt.getVar(), tgt.getMethod(), tgt.getStmt(), SVTEdge.VTEType.VTE_ALIAS);
					/*
					createTransferEdge(tgt.getVar(), tgt.getMethod(), tgt.getStmt(),
							src.getVar(), src.getMethod(), src.getStmt(), SVTEdge.VTEType.VTE_ALIAS);
					*/		
				}
			}
		} // for each alias class
		
		/* create transfer edges between reference formal parameter and actual parameter if the formal
		 * parameter is redefined directly or via alias 
		 */
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
			for (SVTNode n : fparamAliasSet) {
				if (localDefSet.contains(n)) {
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
					Variable avar = new StdVariable(aval);
					Value fval = rudce.getFormalParam(paramIdx).getV();
					//Variable fvar = new CSArgVar(fval, callersite, paramIdx); // here callersite serves a place-holder only
					Variable fvar = new StdVariable(fval);
					
					createTransferEdge(fvar, callee, sIdFormal,
							avar, callersite.getLoc().getMethod(), callersite.getLoc().getStmt(),
							SVTEdge.VTEType.VTE_PARARET);
				}
			}
		} // for each reference parameter
	} // createIntraproceduralValueTransferEdges
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	 /**
     * Save the state of the <tt>SVTG</tt> instance to a stream (i.e.,
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
        	s.writeObject(node.getMethod().getName());
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
     * Reconstitute the <tt>SVTG</tt> instance from a stream (i.e.,
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
        	SVTEdge.VTEType et = (SVTEdge.VTEType)s.readObject();
        	// Read the edge type and instantiate an edge object then add it to the graph
        	createTransferEdge( nodelist.get(src), nodelist.get(tgt), et, false );
        }
        // - 
    }
	
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
	
	public static SVTG DeserializeFromFile(String sfn) {
		SVTG vtg = new SVTG();
		FileInputStream fis;
		try {
			fis = new FileInputStream(sfn);
			
			// reconstruct the static VTG from the given disk file 
			ObjectInputStream ois = new ObjectInputStream(fis);
			vtg = (SVTG) ois.readObject();
			//vtg.readObject(ois);
			
			// --
			return vtg;
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the source file from which the VTG is deserialized specified as " + sfn);
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to SVTG!");
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	} // DeserializeFromFile
	
	/**
	 * for debugging purposes, list all edge details
	 * @param listByEdgeType
	 */
	public void dumpGraphInternals(boolean listByEdgeType) {
		System.out.println(this);
		
		if (!listByEdgeType) {
			/* list all edges */
			for (SVTEdge edge : edges) {
				System.out.println(edge);
			}
			return;
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
			System.out.println("----------------------------------------- " + 
					en.getKey().getName() + " [" +	en.getValue().size() + 
					" nodes] -----------------------------------------");
			for (SVTNode vn : en.getValue()) {
				System.out.println("\t"+vn);
			}
		}
		
		/* list edges by types */
		Map<SVTEdge.VTEType, List<SVTEdge>> type2edges = new LinkedHashMap<SVTEdge.VTEType, List<SVTEdge>>();
		for (SVTEdge edge : edges) {
			List<SVTEdge> els = type2edges.get(edge.getEdgeType());
			if (els == null) {
				els = new LinkedList<SVTEdge>();
				type2edges.put(edge.getEdgeType(), els);
			}
			els.add(edge);
		}
		for (Map.Entry<SVTEdge.VTEType, List<SVTEdge>> en : type2edges.entrySet()) {
			System.out.println("----------------------------------------- " + 
					SVTEdge.edgeTypeLiteral(en.getKey()) + " [" +	en.getValue().size() + 
					" edges] -----------------------------------------");
			for (SVTEdge edge : en.getValue()) {
				System.out.println("\t"+edge);
			}
		}
	} // dumpGraphInternals
	
} // definition of SVTG

/* vim :set ts=4 tw=4 tws=4 */
