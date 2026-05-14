/**
 * File: src/EAS/EAAnalysis.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 05/21/13		hcai		created; for computing method-level impact sets according to EA sequences
 * 05/22/13		hcai		finished and fixed bugs to make it fully work as genuine EAS algorithm did
 * 10/30/13		hcai		ensure trace file to be closed after done reading
 *  
*/
package EAS;
import java.io.*;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

public class EAAnalysis{
	static Set<String> changeSet = new LinkedHashSet<String>();
	static Set<String> impactSet = new LinkedHashSet<String>();
	static int nExecutions = Integer.MAX_VALUE;
	
	static boolean debugOut = false;
	
	public static void main(String args[]){
		if (args.length < 2) {
			System.err.println("Too few arguments: \n\t " +
					"EAAnalysis changedMethods traceDir [numberTraces]\n\n");
			return;
		}
		
		String changedMethods = args[0]; // tell the changed methods, separated by comma if there are more than one
		String traceDir = args[1]; // tell the directory where execution traces can be accessed
		
		// read at most N execution traces if specified, otherwise exhaust all to be found
		if (args.length > 2) {
			nExecutions = Integer.parseInt(args[2]);
		}
		
		if (args.length > 3) {
			debugOut = args[3].equalsIgnoreCase("-debug");
		}
		
		if (debugOut) {
			System.out.println("Try to read [" + (-1==nExecutions?"All available":nExecutions) + "] traces in " 
					+ traceDir + " with changed methods being " + changedMethods);
		}
		
		try {
			
			startParseTraces(changedMethods, traceDir);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void startParseTraces(String changedMethods, String traceDir) {
		int tId;
		List<String> Chglist = dua.util.Util.parseStringList(changedMethods, ';');
		if (Chglist.size() < 1) {
			// nothing to do
			return;
		}
		
		for (tId = 1; tId <= nExecutions; ++tId) {
			String CLT = "";
			Integer tsCLT = Integer.MAX_VALUE;
			
			FileInputStream fis;
			try {
				String fnSource = traceDir  + File.separator + "test"+tId+ ".em";
				fis = new FileInputStream(fnSource);
				if (debugOut) {
					System.out.println("\nDeserializing event maps from " + fnSource);
				}
				
				// 1. reconstruct the two event maps from the serialized execution trace associated with this test
				HashMap<String, Integer> F = new HashMap<String, Integer> ( );
				HashMap<String, Integer> L = new HashMap<String, Integer> ( );
				ObjectInputStream ois = new ObjectInputStream(fis);
				F = extracted(ois);
				L = extracted(ois);
				
				// -- DEBUG
				if (debugOut) {
					System.out.println("\n[ First events ]\n" + F );
					System.out.println("\n[ Last events ]\n" + L );
				}
				
				// 2. determine the CLT (Change with Least Time-stamp in F) 
				List<String> localChgSet = new ArrayList<String>();
				for (String chg : Chglist) {
					for (String m : F.keySet()) {
						if ( !m.toLowerCase().contains(chg.toLowerCase()) && 
								!chg.toLowerCase().contains(m.toLowerCase()) ) {
							// unmatched change specified even with a very loose matching
							continue;
						}
						localChgSet.add(m);
						if (F.get(m) <= tsCLT) {
							tsCLT = F.get(m);
							CLT = m;
						}
					}
				}
				if (localChgSet.isEmpty()) {
					// nothing to do with this execution trace with respect to the given change set
					fis.close();
					ois.close();
					continue;
				}
				changeSet.addAll(localChgSet);
				
				// 3. compute the impact set with respect to this execution trace
				Set<String> localImpactSet = new LinkedHashSet<String>();
				for (String m : L.keySet()) {
					if (L.get(m) >= tsCLT) {
						localImpactSet.add(m);
					}
				}
				if (debugOut) {
					System.out.println("\n============ EAS result from current trace [no. " + tId + "] ================");
					System.out.println("CLT: " + CLT + "[ts=" + tsCLT + "]\n");
					printStatistics(localImpactSet, false);
				}
				// --
				impactSet.addAll(localImpactSet);
				
				fis.close();
				ois.close();
			}
			catch (FileNotFoundException e) { 
				break;
			}
			catch (ClassCastException e) {
				System.err.println("Failed to cast the object deserialized to HashMap<String, Integer>!");
				return;
			}
			catch (IOException e) {
				throw new RuntimeException(e); 
			}
			catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		System.out.println(--tId + " execution traces have been processed.");
		printStatistics(impactSet, true);
	}
	
	/** this method is extracted from above for the purpose of reusing elsewhere */
	public static int parseSingleTrace(String traceDir, int tId, List<String> Chglist, Set<String> localImpactSet) throws Exception {
		String CLT = "";
		Integer tsCLT = Integer.MAX_VALUE;
		
		FileInputStream fis;
		try {
			String fnSource = traceDir  + "/test"+tId+ ".em";
			fis = new FileInputStream(fnSource);
			if (debugOut) {
				System.out.println("\nDeserializing event maps from " + fnSource);
			}
			
			// 1. reconstruct the two event maps from the serialized execution trace associated with this test
			HashMap<String, Integer> F = new HashMap<String, Integer> ( );
			HashMap<String, Integer> L = new HashMap<String, Integer> ( );
			ObjectInputStream ois = new ObjectInputStream(fis);
			F = extracted(ois);
			L = extracted(ois);
			
			// -- DEBUG
			if (debugOut) {
				System.out.println("\n[ First events ]\n" + F );
				System.out.println("\n[ Last events ]\n" + L );
			}
			
			// 2. determine the CLT (Change with Least Time-stamp in F) 
			List<String> localChgSet = new ArrayList<String>();
			for (String chg : Chglist) {
				for (String m : F.keySet()) {
					if ( !m.toLowerCase().contains(chg.toLowerCase()) && 
							!chg.toLowerCase().contains(m.toLowerCase()) ) {
						// unmatched change specified even with a very loose matching
						continue;
					}
					localChgSet.add(m);
					if (F.get(m) <= tsCLT) {
						tsCLT = F.get(m);
						CLT = m;
					}
				}
			}
			if (localChgSet.isEmpty()) {
				// nothing to do with this execution trace with respect to the given change set
				ois.close();
				fis.close();
				return 0;
			}
			//changeSet.addAll(localChgSet);
			
			// 3. compute the impact set with respect to this execution trace
			for (String m : L.keySet()) {
				if (L.get(m) >= tsCLT) {
					localImpactSet.add(m);
				}
			}
			if (debugOut) {
				System.out.println("\n============ EAS result from current trace [no. " + tId + "] ================");
				System.out.println("CLT: " + CLT + "[ts=" + tsCLT + "]\n");
				printStatistics(localImpactSet, false);
			}
			// --
			//impactSet.addAll(localImpactSet);
			ois.close();
			fis.close();
		}
		catch (Exception e) {
			throw e;
		}
		return localImpactSet.size();
	}

	private static HashMap<String, Integer> extracted(ObjectInputStream ois)
			throws IOException, ClassNotFoundException {
		@SuppressWarnings("unchecked")
		HashMap<String, Integer> readObject = (HashMap<String, Integer>) ois.readObject();
		return readObject;
	}
	
	private static void printStatistics (Set<String> impactset, boolean btitle) {
		if (btitle) {
			System.out.println("\n============ Final EAS Result ================");
			System.out.println("[Valid Query Set]");
			for (String m:changeSet) {
				System.out.println(m);
			}
		}
		
		System.out.println("[Impact Set]: size= " + impactset.size());
		for (String m:impactset) {
			System.out.println(m);
		}
	}
}

/* vim :set ts=4 tw=4 tws=4 */
