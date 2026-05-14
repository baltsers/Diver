/**
 * File: src/Diver/DiverInst.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai		created; for instrumenting EAS method events
 * 06/26/13		hcai		incorporate VTG construction toward a complete Diver static analysis phase
 * 06/28/13		hcai		timing VTG construction
 * 07/05/13		hcai		factor reusable code out as common utilities for the whole mcia project 
 * 07/22/13		hcai		handle catch blocks, using adapted DUAForensics that handls catch blocks
 * 08/21/13		hcai		added VTG visualization and automatic validation options
 * 
*/
package Diver;

import dua.Forensics;
import fault.StmtMapper;

import soot.*;
import soot.util.dot.DotGraph;

import EAS.*;

public class DiverInst extends EAInst {
	
	protected static DiverOptions opts = new DiverOptions();
	
	public static void main(String args[]){
		args = preProcessArgs(opts, args);

		DiverInst dvInst = new DiverInst();
		// examine catch blocks
		dua.Options.ignoreCatchBlocks = false;
		dua.Options.skipDUAAnalysis = true;
		
		Forensics.registerExtension(dvInst);
		Forensics.main(args);
	}
	
	@Override protected void init() {
		clsMonitor = Scene.v().getSootClass("Diver.EAMonitor");
		mInitialize = clsMonitor.getMethodByName("initialize");
		mEnter = clsMonitor.getMethodByName("enter");
		mReturnInto = clsMonitor.getMethodByName("returnInto");
		mTerminate = clsMonitor.getMethodByName("terminate");
	}
	
	@Override public void run() {
		System.out.println("Running Diver static analysis");
		// we would want to retrieve the Jimple statement ids for the VTG nodes
		StmtMapper.getCreateInverseMap();
		
		// 1. create the static value transfer graph
		int ret = createVTG();
		
		// 2. instrument EAS events
		if (ret==0) {
			instrument();
		}
	}
	
	private int createVTG() {
		StaticTransferGraph vtg = new StaticTransferGraph();
		try {
			final long startTime = System.currentTimeMillis();
			//if (0==vtg.buildGraph(opts.debugOut())) return 0;
			vtg.setIncludeIntraCD(opts.intraCD);
			vtg.setIncludeInterCD(opts.interCD);
			
			vtg.setExInterCD(opts.exceptionalInterCD);
			vtg.setIgnoreRTECD(opts.ignoreRTECD);
			
			vtg.buildGraph(opts.debugOut());
			final long stopTime = System.currentTimeMillis();
			System.out.println("VTG construction took " + (stopTime - startTime) + " ms");
			/*
			vtg.addControlDependencies(opts.debugOut());
			System.out.println("Computing control dependencies took " + (System.currentTimeMillis() - stopTime) + " ms");
			*/
			
			// DEBUG: validate the static VTG against static forward slice
			if (opts.validateVTG) {
				// as a part of the static VTG validation, automatically check if VTG misses any dependences involving object variables, including
				// library objects
				vtg.checkObjvarDeps();
			}
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
			
		// DEBUG: test serialization and deserialization
		if (opts.serializeVTG) {
			String fn = dua.util.Util.getCreateBaseOutPath() + "staticVtg.dat";
			if ( 0 == vtg.SerializeToFile(fn) ) {
				//if (opts.debugOut()) 
				{
					System.out.println("======== VTG successfully serialized to " + fn + " ==========");
					StaticTransferGraph g = new StaticTransferGraph();
					if (null != g.DeserializeFromFile (fn)) {
						System.out.println("======== VTG loaded from disk file ==========");
						//g.dumpGraphInternals(true);
						System.out.println(g);
					}
				}
			} // test serialization/deserialization
		} // test static VTG construction
		
		// DEBUG: visualize the VTG for paper writing purposes
		if (opts.visualizeVTG) {
			//String dotfn = soot.SourceLocator.v().getOutputDir() + java.io.File.separator + "staticVTG";
			String dotfn = dua.util.Util.getCreateBaseOutPath() + "staticVTG" + DotGraph.DOT_EXTENSION;
			vtg.visualizeVTG(dotfn);
		}
		
		return 0;
	} // -- createVTG
} // -- public class DiverInst  

/* vim :set ts=4 tw=4 tws=4 */

