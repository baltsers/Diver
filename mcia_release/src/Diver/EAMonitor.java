/**
 * File: src/Diver/EAMonitor.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      	Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai			ported from EAS.Monitor; for monitoring method events in EAS
 * 07/03/13		hcai			for Diver, serialized full sequence of events instead of EA seq only
 * 09/04/13		hcai			optimized full trace monitor by using method indexing to reduce memory load
 *								and by multi-segment trace dumping when the trace length goes over specified limit
 * 11/01/13		hcai			added reportOID the instr-reporter for dynamic alias monitoring
 * 11/06/13		hcai			added caching option for object-id monitoring to avoid deadly long dumping for
 *								programs of large execution trace
 * 11/13/13		hcai			supported two levels of dynamic alias monitoring: method level and method-occurrence level
 *
*/
package Diver;

import java.io.*;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeMap;
import java.util.Map;
import java.util.zip.GZIPOutputStream;

/** Monitoring method events in runtime upon 
 * invocations by instrumented probes in the subject
 *
 * For Diver, this monitor captures full sequence of method events. For a uniform basis, also
 * to track two kinds of events only: entrance (first event) and return-into (last event), as EAS does
 */
public class EAMonitor {
	protected static final long CN_LIMIT = 1*1000*1000;
	protected static int g_traceCnt = 0;
	
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
		
		if (cachingOIDs) {
			fnObjectIds = fname + "o";
		}
		resetInternals();
	}
	
	/* for DUAF/Soot to access this class */
	public static void __link() { }
	
	/* clean up internal data structures that should be done so for separate dumping of them, a typical such occasion is doing this per test case */
	private synchronized static void resetInternals() {
		S.clear();
		A.clear();
		if (cachingOIDs) {
			if (!instanceLevel) memCache.clear();
			else memCacheIns.clear();
		}
		
		synchronized (g_index) {
			g_index = 1;
		}
		
		synchronized (g_counter) {
			g_counter = 1;
		}
		
		g_traceCnt = 0;
	}
	
	/* initialize the two maps and the global counter upon the program start event */		
	public synchronized static void initialize() throws Exception{
		S.clear();
		A.clear();
		if (cachingOIDs) {
			if (!instanceLevel) memCache.clear();
			else memCacheIns.clear();
		}
		
		synchronized (g_index) {
			g_index = 1;
		}
		
		synchronized (g_counter) {
			g_counter = 1;
			A.put(g_counter, PROGRAM_START);
			g_counter++;
		}
		
		g_traceCnt = 0;
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
				
				if (g_counter > CN_LIMIT) {
					serializeEvents();
				}
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
				
				if (g_counter > CN_LIMIT) {
					serializeEvents();
				}
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
		// DEBUG ONLY
		Map<Integer, String> idx2me = new LinkedHashMap<Integer, String>();
		for (String me : S.keySet()) {
			idx2me.put(S.get(me), me);
		}
		for (Integer ts : treeA.keySet()) {
			int idx = treeA.get(ts);
			String mname = idx2me.get(Math.abs(idx)) + (idx>0?":i":":e");
			if (idx == PROGRAM_START) mname = "program start";
			if (idx == PROGRAM_END) mname = "program end";
			System.out.println(ts+"\t"+ mname);
		}
	}
	
	protected synchronized static void serializeEvents() {
		/* serialize for later deserialization in the post-processing phase when impact set is to be computed*/
		if ( !fnEventMaps.isEmpty() ) {
			FileOutputStream fos;
			try {
				ByteArrayOutputStream bos = new ByteArrayOutputStream();
				fos = new FileOutputStream(fnEventMaps+(g_traceCnt>0?g_traceCnt:""));
				GZIPOutputStream goos = new GZIPOutputStream(fos);
				ObjectOutputStream oos = new ObjectOutputStream(bos);
				// TreeMap is not serializable as is HashMap
				// for Diver, we need the full sequence of events instead of the EA sequence only
				
				// First we need the method index for indexing methods because the full sequence does not contain method name
				oos.writeObject(S);
				oos.writeObject(A);
				oos.flush();
				oos.close();
				
				goos.write(bos.toByteArray());
				bos.flush();
				bos.close();
				
				goos.flush();
				goos.close();
				
				fos.flush();
				fos.close();
			}
			catch (Exception e) {
				e.printStackTrace();
			}
			finally {
				// we won't allow the confusion of overwriting the file with the event maps from multiple executions 
				//fnEventMaps = "";
				A.clear();
				g_counter = 1;
				g_traceCnt ++;
			}
		}
	}
	
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	/** dump the unique object id of a given object at runtime
	 *	used by DynAliasInst 
	 */
	/** Used to avoid infinite recursion */
	private static boolean active = false;
	public static PrintStream outStream = null;
	/** cache all object ids until the termination of the current execution, when the cached content is to be dumped */
	// At the method level
	public static final Map<dua.util.Pair<Integer, String>, Set<Integer>> memCache = new LinkedHashMap<dua.util.Pair<Integer, String>, Set<Integer>>();
	// At the method-occurrence level
	public static final Map<dua.util.Pair<Integer, String>, Map<Integer, Set<Integer>>> memCacheIns = 
		new LinkedHashMap<dua.util.Pair<Integer, String>, Map<Integer, Set<Integer>>>();
	/** the name of the file to save the dumped cache content */
	protected static String fnObjectIds = "";
	public static void setIdFile(String fname) { fnObjectIds = fname; }
	/* if caching the object ids until the end of execution, or dumping in an immediate manner at each monitoring point */
	public static boolean cachingOIDs = true;
	/* record object ids at method level or method instance level */
	public static boolean instanceLevel = true;
	
	// at the method level
	public synchronized static void reportOID(int sid, String var, Object o) {
	// public synchronized static void reportOID(String m, int sid, String var, Object o) {
		if (active) return;
		active = true;
		if (outStream == null) {
			outStream = System.out;
		}
		try {
			reportOID_impl(sid, var, o);
			// reportOID_impl(m, sid, var, o);
		}
		catch (Throwable t) {
			t.printStackTrace(outStream);
		}
		finally {
			active = false;
		}
	}

	public synchronized static void reportOID_impl(int sid, String var, Object o) {
	//private static volatile String prem = "";
	//private static volatile int mocc = 0;
	//public synchronized static void reportOID_impl(String m, int sid, String var, Object o) {
		int id = 0;
		if (o != null) {
			id = System.identityHashCode(o);
			
			if (cachingOIDs) {
				dua.util.Pair<Integer, String> sidval = new dua.util.Pair<Integer, String>(sid, var);
				// at the method level
				if (!instanceLevel) {
					Set<Integer> ids = memCache.get(sidval);
					if (ids == null) {
						ids = new LinkedHashSet<Integer>();
						memCache.put(sidval, ids);
					}
					ids.add(id);
				}
				// at the method-occurrence level
				else {
					Map<Integer, Set<Integer>> num2ids = memCacheIns.get(sidval);
					if (num2ids == null) {
						num2ids = new LinkedHashMap<Integer, Set<Integer>>();
						memCacheIns.put(sidval, num2ids);
					}
					Set<Integer> ids = num2ids.get(g_counter-1);
					if (ids == null) {
						ids = new LinkedHashSet<Integer>();
						num2ids.put(g_counter-1, ids);
					}
					ids.add(id);
				}
			}
			else {
				//outStream.println(sid+":"+var+" " + id);
				System.out.println(sid+":"+var+" " + id);
			}
		}
	}
	public synchronized static void serializeObjIDCache() {
		if ( !fnObjectIds.isEmpty() ) {
			FileOutputStream fos;
			try {
				fos = new FileOutputStream(fnObjectIds);
				ObjectOutputStream oos = new ObjectOutputStream(fos);
				// at the method level
				if (!instanceLevel) {
					//oos.writeObject(memCache);
					oos.writeInt(memCache.size());
					for (Map.Entry<dua.util.Pair<Integer, String>, Set<Integer>> en : memCache.entrySet()) {
						oos.writeObject(en.getKey().first());
						oos.writeObject(en.getKey().second());
						oos.writeObject(en.getValue());
					}
				}
				// at the method-occurrence level
				else {
					//oos.writeObject(memCacheIns);
					oos.writeInt(memCacheIns.size());
					for (Map.Entry<dua.util.Pair<Integer, String>, Map<Integer, Set<Integer>>> en : memCacheIns.entrySet()) {
						oos.writeObject(en.getKey().first());
						oos.writeObject(en.getKey().second());
						oos.writeObject(en.getValue());
					}
				}
				oos.flush();
				oos.close();
				fos.flush();
				fos.close();
			}
			catch (Exception e) {
				e.printStackTrace();
			}
			finally {
				fnObjectIds = "";
			}
		}
	}
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
}

/* vim :set ts=4 tw=4 tws=4 */

