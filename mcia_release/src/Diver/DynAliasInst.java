/**
 * File: src/Diver/DynAliasInst.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 10/30/13		hcai		created; instrument monitoring dynamic aliasing for heap object edges in MDG
 * 11/01/13		hcai		reached the first workable version 
 * 11/06/13		hcai		fixed a few instrumentation issues with argoUML and Jaba (now works with all seven subjects );
 *							added instrumentation of object-id cache serialization in entry methods
 * 06/27/14		hcai		more thorough fixes of instrumentation for objectID probes for anonymous fields in ctors (for Repo study of Diver with Ant)
*/
package Diver;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import profile.InstrumManager;

import dua.Forensics;
import dua.global.ProgramFlowGraph;
import dua.method.CFGDefUses.ObjVariable;
import dua.method.CFGDefUses.Variable;
import dua.util.Util;
import fault.StmtMapper;

import soot.*;
import soot.jimple.ArrayRef;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;

import MciaUtil.utils;

public class DynAliasInst extends DiverInst {
	
	protected static DiverOptions opts = new DiverOptions();
	
	protected Set<SVTNode> NodesToMonitor = new LinkedHashSet<SVTNode>();
	
	private SootMethod mOIDReporter;
	private SootMethod mCachedContentReporter;
	
	/** if dumping object ids immediately at each instrumented point, or cache them until the termination of program execution */
	public static boolean cachingContent = true;
		
	public static void main(String args[]){
		args = preProcessArgs(opts, args);

		DynAliasInst dvInst = new DynAliasInst();
		cachingContent = opts.cachingOIDs;
		// examine catch blocks
		dua.Options.ignoreCatchBlocks = false;
		
		Forensics.registerExtension(dvInst);
		Forensics.main(args);
	}
	
	@Override protected void init() {
		//clsMonitor = Scene.v().getSootClass("Diver.EAMonitor");
		super.init();
		mOIDReporter = clsMonitor.getMethodByName("reportOID");
		mCachedContentReporter = clsMonitor.getMethodByName("serializeObjIDCache");
	}
	
	@Override public void run() {
		System.out.println("Running DynAlias-Instrumenter extension of DUA-Forensics");
		// we would want to retrieve the Jimple statement ids for the VTG nodes
		StmtMapper.getCreateInverseMap();
		
		// 1. create the static value transfer graph
		int ret = collectInstrumentPoints();
		
		// 2. instrument object id monitoring
		if (ret>0) {
			init();
			for (SVTNode sn : NodesToMonitor) {
				insertMonitorAtNode(sn);
			}
			System.out.println(ret + " objects have been instrumented for aliasing monitoring");
			
			// if chosen, insert the code for reporting the cached content of all object ids
			if (cachingContent) {
				insertCachedContentReporter();
				// 3. EA instrumentation
				super.instrument();
			}
			else {
				if (opts.dumpJimple()) {
					fJimpleInsted = new File(Util.getCreateBaseOutPath() + "JimpleInstrumented.out");
					utils.writeJimple(fJimpleInsted);
				}
			}
		}
	}
	
	private int collectInstrumentPoints() {
		StaticTransferGraph vtg = new StaticTransferGraph();
		try {
			final long startTime = System.currentTimeMillis();
			/*
			vtg.setIncludeIntraCD(opts.intraCD);
			vtg.setIncludeInterCD(opts.interCD);
			
			vtg.setExInterCD(opts.exceptionalInterCD);
			vtg.setIgnoreRTECD(opts.ignoreRTECD);
			*/			
			vtg.buildGraph(opts.debugOut());
			final long stopTime = System.currentTimeMillis();
			System.out.println("VTG construction took " + (stopTime - startTime) + " ms");
		}
		catch (Exception e) {
			System.out.println("Error occurred during the construction of VTG");
			e.printStackTrace();
			return -1;
		}

		if (opts.debugOut()) {
			vtg.dumpGraphInternals(true);
		}
		else {
			System.out.println(vtg);
		}
		
		// collect all MDG nodes where aliasing can be involved as the instrumentation points
		for (SVTNode sn : vtg.nodeSet()) {
			Variable var = sn.getVar();
			if (shouldSkip(sn)) {
				continue;
			}
			
			// we monitor all possible heap objects that can involve aliasing
			if (var.isObject() || var.isFieldRef() || var.isArrayRef()) {
				NodesToMonitor.add(sn);
			}
		}
				
		return NodesToMonitor.size();
	} // -- collectInstrumentPoints
	
	private int insertMonitorAtNode(SVTNode sn) {
		List<Object> monitorProbes = new ArrayList<Object>();
		
		List<Value> enterArgs = new ArrayList<Value>();
		enterArgs.add(IntConstant.v(utils.getFlexibleStmtId(sn.getStmt())));
		enterArgs.add(StringConstant.v(utils.getCanonicalFieldName(sn.getVar())));
		enterArgs.add(makeBoxedVariable(sn.getMethod(), sn.getVar(), monitorProbes));
		
		Stmt sEnterCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mOIDReporter.makeRef(), (List<? extends Value>) enterArgs ));
		monitorProbes.add(sEnterCall);
		
		Stmt s = sn.getStmt();
		PatchingChain<Unit> pchain = sn.getMethod().retrieveActiveBody().getUnits();
		
		// Now, insert the monitor in different locations according to the type of the node hosting statement and its underlying Value;
		// in a way very similar to EH instrumentation
		
		// if node is at a ID stmt, jump to the first non-ID stmt to insert the probe
		if (s instanceof IdentityStmt) {
			InstrumManager.v().insertBeforeNoRedirect(pchain, monitorProbes, 
					utils.getFirstSafeNonIdStmt(sn.getVar().getValue(), sn.getMethod()));
			return 0;
		}
		// if node is at a return stmt, insert probe prior to the return
		if (s instanceof ReturnStmt) {
			InstrumManager.v().insertAtProbeBottom(pchain, monitorProbes, s);
			return 0;
		}
		
		/*
		// if node is at an assignment stmt and it holds a value on the right hand side,  insert probe after the hosting statement if the 
		// value is a special invoke expression and before it otherwise
		if ( s instanceof AssignStmt && ((AssignStmt) s).getLeftOp() instanceof Local && 
				((Local) ((AssignStmt) s).getLeftOp()) != sn.getVar().getValue()) {
			InstrumManager.v().insertAtProbeBottom(pchain, monitorProbes, utils.getAfterSpecialInvokeStmt(pchain, s));
			return 0;
		}
		*/
		
		// for other cases,  insert the probe immediately after the hosting statement (unless a new statement when we need jump after
		// the initialization of the instantiated object is done
		InstrumManager.v().insertBeforeNoRedirect(pchain, monitorProbes, utils.getSuccAfterNextSpecialInvokeStmt(pchain, s)); 
		//InstrumManager.v().insertAfter(pchain, monitorProbes, s);
		
		// - Debugging
		/*
		if (sn.getMethod().getSignature().equalsIgnoreCase("<org.apache.xml.security.test.interop.BaltimoreTest: void main(java.lang.String[])>")) {
			System.out.println(sn.getMethod().retrieveActiveBody());
		}
		*/
		
		return 0;
	}
	
	private boolean shouldSkip(SVTNode sn) {
		/** we don't consider any CD nodes */
		/*
		if (var instanceof MciaUtil.CDEdgeVar) {
			// CDEdgeVar is a type of symbolic variable, it does not represent a real one
			continue;
		}
		
		if (sn.getVar().isFieldRef() && sn.getVar().getValue() instanceof StaticFieldRef) {
			// constant base, no alias
			return true;
		}
		*/
		if (sn.getVar().isObject() && ((ObjVariable)sn.getVar()).getBaseLocal()==null) {
			// no base, no alias
			return true;
		}
		if (sn.getVar().isStrConstObj() || sn.getVar().isConstant()) {
			// a constant won't be aliased
			return true;
		}
		if (sn.getStmt() instanceof InvokeStmt && sn.getVar().getValue() instanceof InvokeExpr) {
			// this kind of nodes won't involve aliasing
			return true;
		}
		
		/*
		Type t = sn.getVar().getValue().getType();
		if (t instanceof RefType && utils.isAnonymousClass(((RefType)t).getSootClass())) {
			System.out.println("object of anonymouse class skipped: " + ((RefType)t).getSootClass());
			return true;
		}
		*/
		
		if (sn.getMethod().getName().equals("<init>")	&& sn.getVar().isFieldRef()) {
			final String fldName = ((FieldRef) sn.getVar().getValue()).getFieldRef().name();
			//if (fldName.equals("this$0")) {
			if (fldName.startsWith("this$") && utils.isAnonymousName(fldName)) {
				return true;
			}
			
			SootClass cls = ((FieldRef)sn.getVar().getValue()).getField().getDeclaringClass(); 
			if (cls.getName().equalsIgnoreCase(sn.getMethod().getDeclaringClass().getName()) && utils.isAnonymousClass(cls)) {
				//if (!((FieldRef)sn.getVar().getValue()).getField().isDeclared() || fldName.startsWith("val$")) 
				{
					return true;
				}
			}
		}
		
		if (sn.getMethod().getName().equals("<clinit>") && sn.getVar().isFieldRef()) {
			final String fldName = ((FieldRef) sn.getVar().getValue()).getFieldRef().name();
			//if (fldName.equals("class$0")) {
			if (fldName.startsWith("class$") && utils.isAnonymousName(fldName)) {
				return true;
			}
		}
		
		return false;
	}
	
	public static Value makeBoxedVariable(SootMethod m, Variable var, List<Object> probe) {
		return makeBoxedVariable(m, var, probe, Scene.v().getSootClass("java.lang.Object").getType());
	}
	public static Value makeBoxedVariable(SootMethod m, Variable var, List<Object> probe, Type tLocalObj) {
		Value v = var.getValue();
		if (var.isObject()) {
			v = ((ObjVariable)var).getBaseLocal();
		}
		else if (var.isFieldRef() && (v instanceof InstanceFieldRef)) {
			v = ((InstanceFieldRef)v).getBase();
		}
		else if (var.isArrayRef()) {
			v = ((ArrayRef)v).getBase();
		}
		assert v != null;
		//assert !(v instanceof StaticFieldRef);
		return utils.makeBoxedValue(m, v, probe, tLocalObj);
	}
	
	private void insertCachedContentReporter() {
		for (SootMethod entryMethod : ProgramFlowGraph.inst().getEntryMethods()) {
			List<Object> probe = new ArrayList<Object>();
			
			Body entryBody = entryMethod.retrieveActiveBody();
			PatchingChain<Unit> pchainEntry = entryBody.getUnits();
			Stmt sEntryLast = (Stmt) pchainEntry.getLast();
			
			// Insert code to invoke report method
			Stmt reportCallStmt = Jimple.v().newInvokeStmt(
					Jimple.v().newStaticInvokeExpr(mCachedContentReporter.makeRef(), new ArrayList<Value>()));
			probe.add(reportCallStmt);
			
			InstrumManager.v().insertAtProbeBottom(pchainEntry, probe, sEntryLast);
		}
	}
	
} // -- public class DynAliasInst  

/* vim :set ts=4 tw=4 tws=4 */
