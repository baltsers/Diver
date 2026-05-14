/**
 * File: src/Diver/PIEAMonitor.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      	Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai			ported from EAS.Monitor; for monitoring method events in EAS
 * 07/03/13		hcai			for Diver, serialized full sequence of events instead of EA seq only
 *
*/
package Diver;

import java.io.*;

import java.util.HashMap;
import java.util.TreeMap;
import java.util.Map;

import EAS.Monitor;
import MciaUtil.MethodEventComparator;

/** Monitoring method events in runtime upon 
 * invocations by instrumented probes in the subject
 *
 * to faithfully reproduce the Execute-After algorithm, use two maps and a global counter
 * to track two kinds of events only: entrance (first event) and return-into (last event)
 */
public class PIEAMonitor extends Monitor {
	/* for DUAF/Soot to access this class */
	public static void __link() { }
	
	/* initialize the two maps and the global counter upon the program start event */		
	public synchronized static void initialize() throws Exception{
		Monitor.initialize();
	}
	
	public synchronized static void enter(String methodname){
		Monitor.enter(methodname);
	}

	/* the callee could be either an actual method called or a trap */
	public synchronized static void returnInto(String methodname, String calleeName){
		Monitor.returnInto(methodname, calleeName);
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

		if (debugOut) {
			dumpEvents();
		}
		
		serializeEvents();
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
				/*
				oos.writeObject(F); 
				oos.writeObject(L);
				*/
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

