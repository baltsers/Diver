/**
 * File: src/Diver/BranchInst.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 10/20/13		hcai		added branch/statement coverage monitoring for Diver - using some facilities provided by DuaF
 * 10/22/13		hcai		reached the first workable version, contingent upon combitant extension to DuaF (in its
 *							InstrumManager::InsertProbeAt, in particular)
 * 10/25/13		hcai		fixed issues found with xmlsec and jmeter
 * 
*/
package Diver;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import profile.BranchInstrumenter;

import EAS.EAInst;
import MciaUtil.CompleteUnitGraphEx;
import MciaUtil.RDFCDBranchEx;
import MciaUtil.utils;

import dua.Extension;
import dua.Forensics;
import dua.Options;
import dua.global.ProgramFlowGraph;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.Branch;
import dua.method.CFGDefUses.Branch.BranchComparator;
import dua.util.Pair;
import dua.util.Util;
import fault.StmtMapper;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;

public class DiverBranchInst extends EAInst {
	/** the map from a method to its exceptional CDG (intraprocedural) */
	private final Map<SootMethod, StaticCDGraphEx> me2CDG = new LinkedHashMap<SootMethod, StaticCDGraphEx>();

	protected static DiverOptions opts = new DiverOptions();
	
	/** the RDF/CD branch analyzer */
	private final static RDFCDBranchEx rdfCDBranchAnalyzer = RDFCDBranchEx.inst();
	
	/** if remove repeated branches in terms of same targets */
	public static boolean removeRepeatedBrs = true;
	
	public static void main(String args[]){
		args = preProcessArgs(opts, args);

		DiverBranchInst dvbrInst = new DiverBranchInst();
		// examine catch blocks
		dua.Options.ignoreCatchBlocks = false;
		
		Forensics.registerExtension(dvbrInst);
		Forensics.main(args);
	}
	
	@Override public void run() {
		System.out.println("Running Diver branch coverage instrumenter of DUA-Forensics");
		
		// 1. dump branch->CD stmts 
		dumpBranchCDStmts();
		
		// 2. instrument branch coverage monitors
		if (opts.dumpJimple()) {
			fJimpleOrig = new File(Util.getCreateBaseOutPath() + "JimpleOrig.out");
			utils.writeJimple(fJimpleOrig);
		}
		
		rdfCDBranchAnalyzer.removeAssistantNodes();
		
		instrumentAllBranches();
		
		if (opts.dumpJimple()) {
			fJimpleInsted = new File(Util.getCreateBaseOutPath() + "JimpleInstrumented.out");
			utils.writeJimple(fJimpleInsted);
		}
	}
	
	protected void dumpBranchCDStmts() {
		// instantiate all intraprocedural CDGs, each per method
		/** don't use the standard algorithm for now: instead, follow the same algorithm of CD 
		 * computation as DuaF - RDF and "other (non-RDF)" CD branches, so the following is commented out*/
		//computeAllIntraCDs();
		
		// determine, for each branch, all stmts that are control dependent on it
		Map<Stmt, Integer> stmtIds = StmtMapper.getWriteGlobalStmtIds();
		List<Branch> allBranches = rdfCDBranchAnalyzer.getAllBranches();
		if (removeRepeatedBrs) {
			allBranches = rdfCDBranchAnalyzer.getAllUniqueBranches();
		}
		Map<Branch, Set<Stmt>> br2cdstmts = rdfCDBranchAnalyzer.buildBranchToCDStmtsMap(allBranches, stmtIds);
		
		String suffix = "branch";
		File fBranchStmt = new File(Util.getCreateBaseOutPath() + "entitystmt.out." + suffix);
		try {
			// write always a new file, deleting previous contents (if any)
			BufferedWriter writer = new BufferedWriter(new FileWriter(fBranchStmt));
			
			// branches are assumed to be ordered by id
			for (Branch br : allBranches) {
				Set<Stmt> relStmts = br2cdstmts.get(br);
				for (Stmt s : relStmts) {
					writer.write(stmtIds.get(s) + " ");
				}
				writer.write("\n");
			}
			
			writer.flush();
			writer.close();
		}
		catch (FileNotFoundException e) { System.err.println("Couldn't write ENTITYSTMT '" + suffix + "' file: " + e); }
		catch (SecurityException e) { System.err.println("Couldn't write ENTITYSTMT '" + suffix + "' file: " + e); }
		catch (IOException e) { System.err.println("Couldn't write ENTITYSTMT '" + suffix + "' file: " + e); }
	}
	
	protected void computeAllIntraCDs() {
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
				
				final StaticCDGraphEx CDGEx = new StaticCDGraphEx();
				CDGEx.turnDebug(opts.debugOut());
				CDGEx.turnSymbolicCD(true);
				CDGEx.setCurDefSet(null);
				CDGEx.compuateIntraproceduralCDs(sMethod, null);
				
				me2CDG.put(sMethod, CDGEx);
			} // for each method
		} // for each class
	} // computeAllIntraCDs
	
	/** instrument branch coverage monitors for all branches */
	protected int instrumentAllBranches() {
		List<Branch> allBranches = rdfCDBranchAnalyzer.getAllBranches();
		if (removeRepeatedBrs) {
			allBranches = rdfCDBranchAnalyzer.getAllUniqueBranches();
		}
		
		// instrument using DuaF facilities
		BranchInstrumenter brInstrumenter = new BranchInstrumenter(true);
		brInstrumenter.instrumentDirect(allBranches, ProgramFlowGraph.inst().getEntryMethods());
		
		return 0;
	} // instrumentAllBranches
}

/* vim :set ts=4 tw=4 tws=4 */

