/**
 * File: src/MciaUtil/CollectEAInstrumenter.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 07/05/13		hcai		created; instrument the method events defined in the genuine CollectEA/EAT tool
 * 
*/
package MciaUtil;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import profile.InstrumManager;

import dua.global.ProgramFlowGraph;
import dua.method.CFG;
import dua.method.CFG.CFGNode;
import dua.method.CallSite;
import dua.util.Util;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.ExceptionalBlockGraph;
import soot.util.*;

/**
 * An instrumenter that inserts probes for monitoring all method events defined in the CollectEA tool 
 */
public class CollectEAInstrumenter {
	/* the monitor class */
	private SootClass clsMonitor;
	/* all the basic event monitors */
	private SootMethod mInitialize;
	private SootMethod mEnter;
	private SootMethod mReturnInto;
	private SootMethod mTerminate;
	/* file used for dumping Jimple code before and after the instrumentation */
	private File fJimpleOrig = null;
	private File fJimpleInsted = null;
	/* a flag indicating if the Program Start event should be probed in the static <clinit> method or not */
	private static boolean bProgramStartInClinit = false;

	/* if dumping Jimple code or not */
	private boolean dumpJimple = false;
	/* if outputting some debug info during the instrumentation */
	private boolean debugOut = false;
	/* if the Program Start event should be probed in the static <clinit> method, if there is such one */
	private boolean sclinit = false;

	public CollectEAInstrumenter() {
	}
	public CollectEAInstrumenter(boolean _dumpJimple, boolean _debugOut, boolean _sclinit) {
		dumpJimple = _dumpJimple;
		debugOut = _debugOut;
		sclinit = _sclinit;
	}
	
	public void instrument(String MonitorClassName) {
		clsMonitor = Scene.v().getSootClass(MonitorClassName);
		mInitialize = clsMonitor.getMethodByName("initialize");
		mEnter = clsMonitor.getMethodByName("enter");
		mReturnInto = clsMonitor.getMethodByName("returnInto");
		mTerminate = clsMonitor.getMethodByName("terminate");
		
		if (dumpJimple) {
			fJimpleOrig = new File(Util.getCreateBaseOutPath() + "JimpleOrig.out");
			utils.writeJimple(fJimpleOrig);
		}
		
		List<SootMethod> entryMes = ProgramFlowGraph.inst().getEntryMethods();
		List<SootClass> entryClses = null;
		if (sclinit) {
			entryClses = new ArrayList<SootClass>();
			for (SootMethod m:entryMes) {
				entryClses.add(m.getDeclaringClass());
			}
		}
		
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
			
			// when there is a static initializer in the entry class, we will instrument the monitor initialize in there instead of the entry method
			boolean hasCLINIT = false;
			if (sclinit) {
				if (entryClses.contains(sClass)) {
					try {
						SootMethod cl = sClass.getMethodByName("<clinit>");
						hasCLINIT = (cl != null);
					}
					catch (Exception e) {
						// if exception was thrown, either because there are more than one such method (ambiguous) or there is none
						hasCLINIT = (e instanceof RuntimeException && e.toString().contains("ambiguous method"));
					}
				}
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
				
				//Body body = sMethod.getActiveBody();
				Body body = sMethod.retrieveActiveBody();
				
				/* the ID of a method to be used for identifying and indexing a method in the event maps of EAS */
				String meId = sClass.getName() +	"::" + sMethod.getName();
				// -- DEBUG
				if (debugOut) {
					System.out.println("\nNow instrumenting method " + meId + "...");
				}
				
				PatchingChain<Unit> pchn = body.getUnits();
				//Chain<Local> locals = body.getLocals();
				
				/* 1. instrument method entry events and program start event */
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);

				List<CFGNode> cfgnodes = cfg.getFirstRealNonIdNode().getSuccs();
				/* the first non-Identity-Statement node is right where we instrument method entrance event */
				CFGNode firstNode = cfg.getFirstRealNonIdNode(), firstSuccessor = cfgnodes.get(0);
				Stmt firstStmt = firstNode.getStmt();

				List<Stmt> enterProbes = new ArrayList<Stmt>();
				List<StringConstant> enterArgs = new ArrayList<StringConstant>();
				
				boolean bInstProgramStart = false;
				if (sclinit) {
					bInstProgramStart = (hasCLINIT && sMethod.getName().equalsIgnoreCase("<clinit>")) || 
														(!hasCLINIT && entryMes.contains(sMethod));
					if (!bProgramStartInClinit) {
						bProgramStartInClinit = (hasCLINIT && sMethod.getName().equalsIgnoreCase("<clinit>"));
					}
				}
				else {
					bInstProgramStart = entryMes.contains(sMethod);
				}
				
				// when "-sclinit" option specified, instrument monitor initialize in <clinit> if any, otherwise in entry method
				if ( bInstProgramStart ) {
					// before the entry method executes, the monitor needs be initialized
					List<StringConstant> initializeArgs = new ArrayList<StringConstant>();
					Stmt sInitializeCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
							mInitialize.makeRef(), initializeArgs ));
					enterProbes.add(sInitializeCall);
					
					// -- DEBUG
					if (debugOut) {
						System.out.println("monitor initialization instrumented at the beginning of Entry method: " + meId);
					}
				} // -- if (entryMes.contains(sMethod))
				
				enterArgs.add(StringConstant.v(meId));
				Stmt sEnterCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
						mEnter.makeRef(), enterArgs ));
				enterProbes.add(sEnterCall);
				
				// -- DEBUG
				if (debugOut) {
					System.out.println("monitor enter instrumented at the beginning of application method: " + meId);
				}
				if ( firstStmt != null ) {
					InstrumManager.v().insertBeforeNoRedirect(pchn, enterProbes, firstStmt);
				}
				else {
					InstrumManager.v().insertProbeAtEntry(sMethod, enterProbes);
				}
				
				/* 2. instrument method returned-into events and program termination event */
				
				// 2.1 normal returns from call sites OUTSIDE any traps (exception catchers) 
				List<CallSite> callsites = cfg.getCallSites();
				int nCandCallsites = 0;
				for (CallSite cs : callsites) {
					if (cs.hasAppCallees() && !cs.isInCatchBlock()) {
						nCandCallsites ++;
					}
				}
				boolean havingFinally = false;
				String bodySource = body.toString();
				if (bodySource.contains("throw") && 
					bodySource.contains(":= @caughtexception") &&
					bodySource.contains("catch java.lang.Throwable from")) {
					// a very naive, probably imprecise but safe, way to determine if there is any finally block in this method
					havingFinally = true;
					System.out.println("finally block exists in method: " + meId);
				}
				
				int nCurCallsite = 0;
				for (CallSite cs : callsites) {
					if (!cs.hasAppCallees()) {
						// only care about application calls
						continue;
					}
					
					if (cs.isInCatchBlock()) {
						// for catch blocks, we always instrument at the beginning of each block, without looking into
						// the call sites inside the block
						continue;
					}
					
					nCurCallsite ++;
					// -- DEBUG
					if (debugOut) {
						System.out.println("monitor returnInto instrumented at call site " +
								cs + " in method: " + meId);
					}
					
					List<Stmt> retinProbes = new ArrayList<Stmt>();
					List<StringConstant> retinArgs = new ArrayList<StringConstant>();
					retinArgs.add(StringConstant.v(meId));
					retinArgs.add(StringConstant.v(/*cs.getLoc().toString()*/
							cs.hashCode() + ": returnInto after calling " + cs.getAppCallees().get(0).getName()));
					Stmt sReturnIntoCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
							mReturnInto.makeRef(), retinArgs ));
					retinProbes.add(sReturnIntoCall);
					
					// before the entry method finishes, method events are to be dumped
					// -- the exit point of the entry method is regarded as the program end point

					// if there is no any finally block in the entry method, we probe for monitor terminate after the last call site
					if (!havingFinally && nCurCallsite==nCandCallsites && entryMes.contains(sMethod)) {	
						List<StringConstant> terminateArgs = new ArrayList<StringConstant>();
						terminateArgs.add(StringConstant.v(/*cs.getLoc().toString()*/
								cs.hashCode() + ": terminate after calling " + cs.getAppCallees().get(0).getName()));
						Stmt sTerminateCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
								mTerminate.makeRef(), terminateArgs ));
						//retinProbes.add(sTerminateCall);
						
					    // -- DEBUG
						if (debugOut) {
							System.out.println("monitor terminate instrumented at last app call site " +
									cs + " in method: " + meId);
						}
					}
					InstrumManager.v().insertAfter(pchn, retinProbes, cs.getLoc().getStmt());
				}
				
				BlockGraph bg = new ExceptionalBlockGraph(body);
				//List<Block> exitBlocks = bg.getTails();
				Map<Stmt, Stmt> cbExitStmts = new LinkedHashMap<Stmt, Stmt>(); // a map from head to exit of each catch block
				for (Block block : bg.getBlocks()) {
					//block.getTail();
					Stmt head = (Stmt)block.getHead(), curunit = head, exit = curunit;
					if ( head.toString().contains(":= @caughtexception") ) {	
						while (curunit != null) {
							exit = curunit;
							curunit = (Stmt)block.getSuccOf(curunit);
						}
						cbExitStmts.put(head, exit);
					}
				}
				
				// 2.2 catch blocks and finally blocks
				Chain<Trap> traps = body.getTraps();
				if (traps.size() < 1) {
					// no catchers, no catch block instrumentation
					//continue;
				}
				
				// record instrumentation targets to avoid repetitive instrumentation
				Set<Unit> instTargets = new LinkedHashSet<Unit>();
				for (Iterator<Trap> trapIt = traps.iterator(); trapIt.hasNext(); ) {
				    Trap trap = trapIt.next();

				    // instrument at the beginning of each catch block
				    // -- DEBUG
					if (debugOut) {
						System.out.println("monitor returnInto instrumented at the beginning of catch block " +
								trap + " in method: " + meId);
					}
					
					List<Stmt> retinProbes = new ArrayList<Stmt>();
					List<StringConstant> retinArgs = new ArrayList<StringConstant>();
					retinArgs.add(StringConstant.v(meId));
					retinArgs.add(StringConstant.v(/*trap.toString()*/
							trap.hashCode() + ": returnInto in catch block for " + trap.getException().getName()));
					Stmt sReturnIntoCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
							mReturnInto.makeRef(), retinArgs ));
					retinProbes.add(sReturnIntoCall);
					
				    //InstrumManager.v().insertBeforeNoRedirect(pchn, retinProbes, (Stmt)trap.getHandlerUnit());
					Stmt instgt = (Stmt)trap.getHandlerUnit();
					if (!instTargets.contains(instgt)) {
						InstrumManager.v().insertAfter (pchn, retinProbes, instgt);
						instTargets.add(instgt);
					}
					
					// instrument at the beginning of each finally block if any
					if (havingFinally) {
						if (trap.getHandlerUnit().equals(trap.getEndUnit())) {
							// we don't need instrument the probes at the same point twice
							// -- note that for a same TRY statement, the beginning of the finally block, which is trap.getEndUnit(),
							// might be equal to the beginning of a catch block
							continue;
						}
						/* whenever there is a finally block for a TRY statement (maybe without any catch block),
						 *   the block will be copied to the end of every trap; So we can just instrument at the end of
						 *   each of these traps to meet the requirement of instrumenting in each finally block
						 */
						List<Stmt> retinProbesF = new ArrayList<Stmt>();
						List<StringConstant> retinArgsF = new ArrayList<StringConstant>();
						retinArgsF.add(StringConstant.v(meId));
						retinArgsF.add(StringConstant.v(/*trap.toString() */
								trap.getEndUnit().hashCode() + ": returnInto in finally block for " + trap.getException().getName()));
						Stmt sReturnIntoCallF = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
								mReturnInto.makeRef(), retinArgsF ));
						retinProbesF.add(sReturnIntoCallF);
						// -- DEBUG
						if (debugOut) {
							System.out.println("monitor returnInto instrumented at the beginning of the finally block " +
									trap.getEndUnit() + " in method: " + meId);
						}
						// again, avoid repetitive instrumentation although it does not affect the algorithm's correctness of EAS
						if (!((Stmt)trap.getEndUnit()).toString().contains("Diver.EAMonitor: void returnInto")) {
							InstrumManager.v().insertBeforeRedirect (pchn, retinProbesF, (Stmt)trap.getEndUnit());
						}
					}
					else if (entryMes.contains(sMethod)) {
						// if there is no finally block in the entry method, we can safely insert the probe for termination event
						// after the end of each catch block
						List<Stmt> terminateProbes = new ArrayList<Stmt>();
						List<StringConstant> terminateArgs = new ArrayList<StringConstant>();
						terminateArgs.add(StringConstant.v(/*trap.toString()*/
								trap.hashCode() + ": terminate in catch block for " + trap.getException().getName()));
						Stmt sTerminateCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
								mTerminate.makeRef(), terminateArgs ));
						terminateProbes.add(sTerminateCall);
						// -- DEBUG
						if (debugOut) {
							System.out.println("monitor terminate instrumented after the end of catch block " +
									trap + " in method: " + meId);
						}
						// if a monitor probe has already become the end unit, we should insert this termination probe after that point
						if (((Stmt)trap.getEndUnit()).toString().contains("Diver.EAMonitor: void returnInto")) {
							//InstrumManager.v().insertAfter (pchn, terminateProbes, (Stmt)trap.getEndUnit());
						}
						// otherwise, just insert right before the last unit of the catch block
						else {
							Stmt cbHead = (Stmt)trap.getHandlerUnit(); // the handler unit is the beginning unit of the catch block
							assert cbExitStmts.containsKey(cbHead);
							Stmt tgt = cbExitStmts.get(cbHead);
							if (tgt instanceof GotoStmt /*&& !(tgt instanceof IdentityStmt)*/) {
								//InstrumManager.v().insertBeforeRedirect (pchn, terminateProbes, tgt);
							}
							else {
								//InstrumManager.v().insertAfter (pchn, terminateProbes, tgt);
							}
						}
					}
				}
				
				// Thus far, we have not insert probe for termination event in the entry method if there is any finally blocks in there
				if (entryMes.contains(sMethod) /*&& havingFinally*/) {
					Set<Stmt> fTargets = new LinkedHashSet<Stmt>();
					Stmt lastThrow = null;
					for (Unit u : pchn) {
						Stmt s = (Stmt)u;
						if (havingFinally) {
							// if the finally block is to be executed after an uncaught exception was thrown, a throw statement 
							// will be the exit point; However, we only probe at the last such finally block if there is no any app call site following it  
							if (s instanceof ThrowStmt) {
								//System.out.println("Got a throw statement " + s);
								lastThrow = s;
							}
							if (lastThrow != null) {
								if (ProgramFlowGraph.inst().getNode(s).hasAppCallees()) {
									lastThrow = null;
								}
							}
						}
						
						// In Jimple IR, any method has exactly one return statement
						if (dua.util.Util.isReturnStmt(s)) {
							fTargets.add(s);
						}
					}
					if (lastThrow != null) {
						//fTargets.add(lastThrow);
					}
					assert fTargets.size() >=1 ;
					for (Stmt tgt : fTargets) {
						List<Stmt> terminateProbe = new ArrayList<Stmt>();
						List<StringConstant> terminateArgs = new ArrayList<StringConstant>();
						String flag =  (dua.util.Util.isReturnStmt(tgt)?"return":"throw") + " statement";
						terminateArgs.add(StringConstant.v("terminate in finally block before " + flag));
						Stmt sTerminateCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(
								mTerminate.makeRef(), terminateArgs ));
						terminateProbe.add(sTerminateCall);
						// -- DEBUG
						if (debugOut) {
							System.out.println("monitor termination instrumented at the end of the finally block in " + 
									meId + " before " + flag);
						}
						InstrumManager.v().insertBeforeRedirect (pchn, terminateProbe, tgt);
					}
				}
				
			} // -- while (meIt.hasNext()) 
			
		} // -- while (clsIt.hasNext())
		
		if (dumpJimple) {
			fJimpleInsted = new File(Util.getCreateBaseOutPath() + "JimpleInstrumented.out");
			utils.writeJimple(fJimpleInsted);
		}

		// important warning concerning the later runs of the instrumented subject
		if (bProgramStartInClinit) {
			System.out.println("\n***NOTICE***: program start event probe has been inserted in EntryClass::<clinit>(), " +
					"the instrumented subject MUST thereafter run independently rather than via DiverRun!");
		}
	
	} // -- void instrument()
	
} // -- public class CollectEAInstrumenter

/* vim :set ts=4 tw=4 tws=4 */

