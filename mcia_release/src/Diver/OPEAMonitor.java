/**
 * File: src/Diver/OPEAMonitor.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      	Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai			ported from EAS.Monitor; for monitoring method events in EAS
 * 07/03/13		hcai			for Diver, serialized full sequence of events instead of EA seq only
 * 09/04/13		hcai			optimized full trace monitor that uses method indexing to reduce memory load
 *
*/
package Diver;

import java.io.*;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.TreeMap;
import java.util.Map;

import MciaUtil.MethodEventComparator;

/** Monitoring method events in runtime upon 
 * invocations by instrumented probes in the subject
 *
 * For Diver, this monitor captures full sequence of method events. For a uniform basis, also
 * to track two kinds of events only: entrance (first event) and return-into (last event), as EAS does
 */
public class OPEAMonitor {
	/* the full list of functions which the full event map will index for retrieving the functions (their signature) themselves */
	protected static HashMap<String, Integer> S = new LinkedHashMap<String, Integer>();
	protected static Integer g_index = 1;
	
	/* all events */
	protected static HashMap<Integer, Integer> A = new LinkedHashMap<Integer, Integer>();
	
	/* two special events */
	public static final int PROGRAM_START = Integer.MIN_VALUE;
	public static final int PROGRAM_END = Integer.MAX_VALUE;
	
	/* the global counter for time-stamping each method event */
	protected static Integer g_counter = 0;
	
	/* debug flag: e.g. for dumping event sequence to human-readable format for debugging purposes, etc. */
	protected static boolean debugOut = false;
	public static void turnDebugOut(boolean b) { debugOut = b; } 

	/* output file for serializing the two event maps */
	protected static String fnEventMaps = "";

	/* a flag ensuring the initialization and termination are both executed exactly once and they are paired*/
	protected static boolean bInitialized = false;
	
	/* The name of serialization target file will be set by EARun via this setter */
	public static void setEventMapSerializeFile(String fname) {
		fnEventMaps = fname;
	}
	
	/* for DUAF/Soot to access this class */
	public static void __link() { }
	
	/* initialize the two maps and the global counter upon the program start event */		
	public synchronized static void initialize() throws Exception{
		S.clear();
		A.clear();
		synchronized (g_index) {
			g_index = 1;
		}
		
		synchronized (g_counter) {
			g_counter = 1;
			A.put(g_counter, PROGRAM_START);
			g_counter++;
		}
		
		bInitialized = true;
	}
	
	public synchronized static void enter(String methodname){
		try {
			synchronized (g_index) {
				if (!S.containsKey(methodname)) {
					S.put(methodname, g_index);
					g_index ++;
				}
			}
			synchronized (g_counter) {
				assert S.containsKey(methodname);
				A.put(g_counter, S.get(methodname)*-1);  // negative index for entry event
				g_counter ++;
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/* the callee could be either an actual method called or a trap */
	public synchronized static void returnInto(String methodname, String calleeName){
		try {
			synchronized (g_counter) {
				assert S.containsKey(methodname);
				A.put(g_counter, S.get(methodname)*1);  // positive index for returned-into event
				g_counter ++;
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static Object getMap() { return A.clone(); }
	
	/* 
	 * dump the Execute-After sequence that is converted from the two event maps 
	 * upon program termination event 
	 * this is, however, not required but useful for debugging 
	 *
	 */
	public synchronized static void terminate(String where) throws Exception {
		/** NOTE: we cannot call simply forward this call to super class even though we do the same thing as the parent, because
		 * we need take effect the overloaded SerializeEvents() here below 
		 */
		//Monitor.terminate(where);
		if (bInitialized) {
			bInitialized = false;
		}
		else {
			return;
		}

		synchronized (g_counter) {
			A.put(g_counter, PROGRAM_END);
		}
		
		if (debugOut) {
			dumpEvents();
		}
		
		serializeEvents();
	}
	
	protected synchronized static void dumpEvents() {
		System.out.println("\n[ Method Index ]\n");
		System.out.println(S);
		System.out.println("\n[ Full Sequence of Method Entry and Returned-into Events]\n");
		TreeMap<Integer, Integer> treeA = new TreeMap<Integer, Integer> ( A );
		System.out.println(treeA);
	}
	
	protected synchronized static void serializeEvents() {
		/* serialize for later deserialization in the post-processing phase when impact set is to be computed*/
		if ( !fnEventMaps.isEmpty() ) {
			FileOutputStream fos;
			try {
				fos = new FileOutputStream(fnEventMaps);
				ObjectOutputStream oos = new ObjectOutputStream(fos);
				// TreeMap is not serializable as is HashMap
				// for Diver, we need the full sequence of events instead of the EA sequence only
				
				// First we need the method index for indexing methods because the full sequence does not contain method name
				oos.writeObject(S);
				oos.writeObject(A);
				oos.flush();
				oos.close();
			}
			catch (Exception e) {
				e.printStackTrace();
			}
			finally {
				// we won't allow the confusion of overwriting the file with the event maps from multiple executions 
				fnEventMaps = "";
			}
		}
	}
}

/* vim :set ts=4 tw=4 tws=4 */

