/**
 * File: src/Diver/DiverAnalysis.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai		created; for computing method-level impact sets according to EA sequences
 * 07/10/13		hcai		1st runnable post-processing
 * 07/22/13		hcai		reached the complete workable version of CD-less Diver after many bug fixes;
 * 07/23/13		hcai		added option to choose one of the three possible impact set computations:
 *							1: pruning; 2: source-target matching, one dynamic VTG exercised by an execution trace
 *							is computed for any later queries; 3: source-target matching, one dynamic VTG for a single
 *							query
 * 10/18/13		hcai		factored into independent components so that they are reusable elsewhere
 * 10/25/13		hcai		applied runtime coverage pruning
 * 11/04/13		hcai		added options for either pre-pruning or post-pruning the MDG nodes and edges according to
 *							coverage information
 * 11/08/13		hcai		applied dynamic alias monitoring data to impact computation
 * 11/13/13		hcai		supported two levels of dynamic alias monitoring: method level and method-occurrence level,
 *							in addition to both static-MDG pruning and dynamic-MDG pruning
 * 11/18/13		hcai		added option for combining statement coverage with dynamic alias data (on method instance level) for impact computation
 * 11/22/13		hcai		further extended for combining statement coverage with dynamic alias data (on method level) for impact computation
 * 12/10/13		hcai		added supports for querying impacts of multi-method changes
 *  
*/
package Diver;
import java.io.*;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class DiverAnalysis{
	static Set<String> changeSet = new LinkedHashSet<String>();
	static Map<String, Set<String> > impactSets = new LinkedHashMap<String, Set<String>>();
	static int nExecutions = Integer.MAX_VALUE;
	
	/* the dynamic transfer graph underneath the impact computation with all execution traces */
	static final DynTransferGraph dvtg = new DynTransferGraph();
	/*
	// the backup of the first successfully loaded static VTG as the initial dynamic VTG
	static final DynTransferGraph dvtgBackup = new DynTransferGraph();
	*/
	
	static boolean debugOut = false;
	
	/** "oneForAll" means per execution trace, we calculate one dynamic VTG that is applicable for any change queries; 
	 *   for now, this dynamic VTG can be as conservative as thus not quite precise;
	 *   as opposed to this choice, the alternative is to compute a dynamic VTG per execution trace per single change query, 
	 *   which, since we know the change query in advance before computing this dynamic VTG, is more precise than "oneForAll"
	 *   as is implemented for now.
	 */
	// TODO: optimization - compute a dynamic VTG per execution trace that is applicable for any change query;
	// or compute impact sets for multiple queries at the same time when traversing the execution trace for only once
	static boolean matchingDynVTGForAllQueries = false;
	// include the pruning approach just for a comparison
	static boolean pruningDynVTGForAllQueries = false;
	
	/** if applying runtime statement coverage information to prune statements not executed, examined per test case */
	public static boolean applyStatementCoverage = false;
	/** prune non-covered/non-aliased nodes and edges prior to or after basic querying process: 
	 * both are equivalent in terms of eventual impact set but can be disparate in performance
	 */
	public static boolean postPrune = true;
	
	/** if applying runtime object alias checking to prune heap value edges on which the source 
	 * and target nodes are not dynamically aliased 
	 */
	public static boolean applyDynAliasChecking = false;
	/** if pruning based on the dynamic alias information at the method instance level, or just the method level */
	public static boolean instancePrune = true; 
	
	public static void main(String args[]){
		if (args.length < 3) {
			System.err.println("Too few arguments: \n\t " +
					"DiverAnalysis changedMethods traceDir binDir [numberTraces] [debugFlag]\n\n");
			return;
		}
		
		String changedMethods = args[0]; // tell the changed methods, separated by comma if there are more than one
		String traceDir = args[1]; // tell the directory where execution traces can be accessed
		String binDir = args[2]; // tell the directory where the static value transfer graph binary can be found
		
		// read at most N execution traces if specified, otherwise exhaust all to be found
		if (args.length > 3) {
			nExecutions = Integer.parseInt(args[3]);
		}
		
		if (args.length > 4) {
			applyStatementCoverage = args[4].equalsIgnoreCase("-stmtcov");
			applyDynAliasChecking = args[4].equalsIgnoreCase("-dynalias");
		}
		
		if (args.length > 5) {
			postPrune = args[5].equalsIgnoreCase("-postprune"); // secondary option working with only "-stmtcov"
			instancePrune = args[5].equalsIgnoreCase("-instanceprune"); // secondary option working with only "-dynalias"
		}
		
		// apply both statement coverage and dynamic alias data, using the best secondary options (postprune and instanceprune respectively) for each
		if (args.length > 4 && args[4].equalsIgnoreCase("-stmtcovdynalias")) {
			applyStatementCoverage = applyDynAliasChecking = true;
			postPrune /*= instancePrune*/ = true;
		}
		
		if (args.length > 6) {
			debugOut = args[6].equalsIgnoreCase("-debug");
		}
		
		if (args.length > 7) {
			matchingDynVTGForAllQueries = args[7].equalsIgnoreCase("-matchingForAll");
			pruningDynVTGForAllQueries = args[7].equalsIgnoreCase("-pruningForAll");
		}
		
		if (debugOut) {
			System.out.println("Try to read [" + (-1==nExecutions?"All available":nExecutions) + "] traces in " 
					+ traceDir + " with changed methods being " + changedMethods);
		}
		
		// initialize the dynamic VTG with the static counterpart
		if (init(binDir) != 0) {
			// something wrong during the initialization of the dynamic graph
			return;
		}
		
		try {
			
			startParseTraces(changedMethods, traceDir);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static int init(String binDir) {
		dvtg.setSVTG(binDir+File.separator+"staticVtg.dat");
		if (0 != dvtg.initializeGraph(debugOut)) {
			System.out.println("Unable to load the static value transfer graph, aborted now.");
			return -1;
		}
		/*
		// backup for recovering when necessary
		dvtgBackup.deepCopyFrom(dvtg);
		*/
		
		// if adopting "reaching impact propagation"
		DynTransferGraph.reachingImpactPropagation = false;
		return 0;
	}
	
	/** read per-test runtime statement coverage information */
	public static int readStmtCoverage(String traceDir, int tId, List<Integer> coveredStmts) {
		String fnOut = traceDir  + File.separator + "test" + tId + ".out";
		String startMark = "Statements covered (based on branch coverage):";
		coveredStmts.clear();
		try {
			FileReader frdOut = new FileReader(new File(fnOut));
			BufferedReader rin = new BufferedReader(frdOut);
			while (true) {
				String strLine = rin.readLine();
				if (strLine == null) break;
				
				//if (strLine.startsWith(startMark)) {
				if (strLine.contains(startMark)) {
					String sub = strLine.substring(strLine.indexOf(startMark)+startMark.length()+1);
					List<String> stmtIds = dua.util.Util.parseStringList(sub,' ');
					//String[] stmtIds = sub.split(" ");
					for (String id : stmtIds) {
						coveredStmts.add (Integer.valueOf(id));
					}
					break;
				}
			}
			
			rin.close();
			frdOut.close();
		}
		catch (Exception e) { 
			System.err.println("Error occurred when reading runtime coverage report from " + fnOut);
			return -1;
		}
		
		return coveredStmts.size();
	}
	
	/** read per-test runtime statement coverage information */
	// at the method level
	public static int readObjectIDs(String traceDir, int tId, Map<dua.util.Pair<Integer, String>, Set<Integer>> objIDs) {
		String fnEmo = traceDir  + File.separator + "test" + tId + ".emo";
		objIDs.clear();
		FileInputStream fis;
		try {
			fis = new FileInputStream(fnEmo);
			ObjectInputStream ois = new ObjectInputStream(fis);
			int size = ois.readInt();
			for (int i = 0; i < size; i++) {
				Integer sid = (Integer)ois.readObject();
				String val = (String)ois.readObject();
				@SuppressWarnings("unchecked")
				Set<Integer> ids = (LinkedHashSet<Integer>)ois.readObject();

				objIDs.put(new dua.util.Pair<Integer, String>(sid, val), ids);
			}
			ois.close();
			fis.close();
		}
		catch (Exception e) {
			System.err.println("Error occurred when reading the dumped object ids from " + fnEmo);
			return -1;
		}
		
		return objIDs.size();
	}
	public static int readObjectIDMaps(String traceDir, int tId, Map<dua.util.Pair<Integer, String>, Map<Integer,Set<Integer>>> objIDs) {	
		String fnEmo = traceDir  + File.separator + "test" + tId + ".emo";
		objIDs.clear();
		FileInputStream fis;
		try {
			fis = new FileInputStream(fnEmo);
			ObjectInputStream ois = new ObjectInputStream(fis);
			int size = ois.readInt();
			for (int i = 0; i < size; i++) {
				Integer sid = (Integer)ois.readObject();
				String val = (String)ois.readObject();
				@SuppressWarnings("unchecked")
				Map<Integer, Set<Integer>> idmap = (LinkedHashMap<Integer, Set<Integer>>) ois.readObject(); 

				objIDs.put(new dua.util.Pair<Integer, String>(sid, val), idmap);
			}
			ois.close();
			fis.close();
		}
		catch (Exception e) {
			System.err.println("Error occurred when reading the dumped object ids from " + fnEmo);
			return -1;
		}
		
		return objIDs.size();
	}
	
	public static int updateGraphWithCoverage(String traceDir, int tId) {
		if (applyStatementCoverage) {
			List<Integer> coveredStmts = new ArrayList<Integer>();
			if (readStmtCoverage(traceDir, tId, coveredStmts) <= 0) {
				// nothing to do further along
				System.err.println("Error: empty coverage with test No. " + tId);
				return -1;
			}
			// prune the initial dynamic VTG
			int nPrunedEdges = dvtg.reInitializeGraph(DynTransferGraph.svtg, coveredStmts);
			if (debugOut) {
				System.out.println("\n Statement coverage pruned " + nPrunedEdges + 
						" edges in the static graph before querying.");
			}
			return nPrunedEdges;
		}
		return 0;
	}
	
	/** exercise the static graph and query impacts for a single execution trace */
	public static int parseSingleTrace(String traceDir, int tId, List<String> validChgSet, 
			Map<String, Set<String>> localImpactSets) throws Exception {
		try {
			String fnSource = traceDir  + File.separator + "test" + tId + ".em";
			if (debugOut) {
				System.out.println("\nProcessing execution trace in " + fnSource);
			}
			
			// 1. compute the dynamic VTG using the current execution trace
			dvtg.setTrace(fnSource);
			/*final*/ DynTransferGraph dvtgExercised = new DynTransferGraph();
			/*
			dvtg.CopyFrom(dvtgBackup);
			*/
			if (matchingDynVTGForAllQueries) {
				if (0 != dvtg.buildGraph(dvtgExercised,false)) {
				//if (0 != dvtg.buildGraph(dvtgExercised,debugOut)) {	
					System.out.println("\nExecution trace in " + fnSource + " was NOT successfully processed, skipped therefore.");
					return -1;
				}
				
				if (debugOut) {
					System.out.println("dynamic VTG exercised by current trace: ");
					//dvtgExercised.dumpGraphInternals(true);
					System.out.println(dvtgExercised);
				}
			}
			else if (pruningDynVTGForAllQueries) {
				if (0 != dvtg.pruneGraph(dvtgExercised,false)) {
				//if (0 != dvtg.pruneGraph(dvtgExercised,false)) {
						System.out.println("\nExecution trace in " + fnSource + " was NOT successfully processed, skipped therefore.");
						return -1;
					}
					
					if (debugOut) {
						System.out.println("dynamic VTG exercised by current trace: ");
						//dvtgExercised.dumpGraphInternals(true);
						System.out.println(dvtgExercised);
					}
			}
			
			// 2. compute the local impact set : the impact set with respect to the current execution trace
			for (String chg : validChgSet) {
				if (applyDynAliasChecking && instancePrune) {
					Map<dua.util.Pair<Integer, String>, Map<Integer, Set<Integer>>> objIDMaps = 
						new  LinkedHashMap<dua.util.Pair<Integer, String>, Map<Integer, Set<Integer>>>();
					if (readObjectIDMaps(traceDir, tId, objIDMaps) <= 0) {
						// nothing to do further along
						System.err.println("Error: empty object id map with test No. " + tId);
						continue;
					}
					dvtg.objIDMaps = objIDMaps;
					//dvtg.nPrunedEdgeByObjID = 0;
					dvtg.prunedByOID.clear();
				}
				
				if (!matchingDynVTGForAllQueries && !pruningDynVTGForAllQueries) {
					if (0 != dvtg.buildGraph(dvtgExercised, chg, false)) {
						System.out.println("\nExecution trace in " + fnSource + " was NOT successfully processed, skipped therefore.");
						continue;
					}
					if (debugOut) {
						System.out.println("dynamic VTG exercised by current trace and change query [" + chg + "] :");
						//dvtgExercised.dumpGraphInternals(true);
						System.out.println(dvtgExercised);
						if (applyDynAliasChecking && instancePrune) {
							int nPrunedEdges = dvtg.prunedByOID.size(); //dvtg.nPrunedEdgeByObjID;
							System.out.println("\n Object-id matching pruned " + nPrunedEdges 
									+ 	" edges in the dynamic graph during the querying process.");
						}
					}
				}
				 
				Set<String> is = localImpactSets.get(chg);
				if (null == is) {
					is = new LinkedHashSet<String>();
					localImpactSets.put(chg, is);
				}
				
				// prune the exercised dynamic VTG with coverage information
				if (applyStatementCoverage && postPrune) {
					List<Integer> coveredStmts = new ArrayList<Integer>();
					if (readStmtCoverage(traceDir, tId, coveredStmts) <= 0) {
						// nothing to do further along
						System.err.println("Error: empty coverage with test No. " + tId);
						continue;
					}
					// prune the exercised dynamic VTG
					final DynTransferGraph dvtgPruned = new DynTransferGraph();
					int nPrunedEdges = dvtgExercised.postPruneByCoverage(dvtgPruned, coveredStmts);
					if (debugOut) {
						System.out.println("\n Statement coverage pruned " + nPrunedEdges + 
								" edges in the dynamic graph after it being exercised.");
					}
					
					if (applyDynAliasChecking && !instancePrune) {
						dvtgExercised = dvtgPruned;
					}
					else {
						is.addAll(dvtgPruned.getImpactSet(chg));
						continue;
					}
				}
				
				// a coarse method level pruning based on dynamic alias monitoring (object-id matching)
				if (applyDynAliasChecking && !instancePrune) {
					Map<dua.util.Pair<Integer, String>, Set<Integer>> objIDs = 
						new  LinkedHashMap<dua.util.Pair<Integer, String>, Set<Integer>>();
					
					if (readObjectIDs(traceDir, tId, objIDs) <= 0) {
						// nothing to do further along
						System.err.println("Error: empty object id map with test No. " + tId);
						continue;
					}
					// prune the exercised dynamic VTG
					final DynTransferGraph dvtgPruned = new DynTransferGraph();
					int nPrunedEdges = dvtgExercised.postPruneByObjIDs(dvtgPruned, objIDs);
					if (debugOut) {
						System.out.println("\n Object-id matching pruned " + nPrunedEdges + 
								" edges in the dynamic graph after it being exercised.");
					}
					
					is.addAll(dvtgPruned.getImpactSet(chg));
					continue;
				}
				
				is.addAll(dvtgExercised.getImpactSet(chg));
				//is.addAll(dvtg.getImpactSet(chg));
			}
		}
		catch (Exception e) {
			throw e;
		}
		return localImpactSets.size();
	}
	
	public static int obtainValidChangeSet(String changedMethods) {
		changeSet.clear();  // in case this method (startParseTraces) gets multiple invocations from external callers 
		List<String> Chglist = dua.util.Util.parseStringList(changedMethods, ';');
		if (Chglist.size() < 1) {
			// nothing to do
			System.err.println("Empty query, nothing to do.");
			return -1;
		}
		// determine the valid change set
		Set<String> validChgSet = new LinkedHashSet<String>();
		for (String chg : Chglist) {
			validChgSet.addAll(dvtg.getChangeSet(chg));
		}
		if (validChgSet.isEmpty()) {
			// nothing to do
			// System.out.println("Invalid queries, nothing to do.");
			return 0;
		}
		changeSet.addAll(validChgSet);
		return changeSet.size();
	}
	public static Set<String> getChangeSet() {
		return changeSet;
	}
	
	public static void startParseTraces(String changedMethods, String traceDir) {
		int tId;
		impactSets.clear(); // in case this method (startParseTraces) gets multiple invocations from external callers
		
		int nret = obtainValidChangeSet(changedMethods);
		if ( nret <= 0 ) {
			// nothing to do
			if (nret == 0) {
				// always output report so that post-processing script can work with the Diver result in a consistent way as if there were
				// some non-empty results
				printStatistics(impactSets, true);
			}
			return;
		}
		
		for (tId = 1; tId <= nExecutions; ++tId) {
			// impact sets relative to the current execution trace
			Map<String, Set<String>> localImpactSets = new LinkedHashMap<String, Set<String>>();
			
			try {
				// if statement coverage applied, rebuild the initial dynamic VTG and take the chance to prune nodes and edges
				// associated with statements that are not covered by this test case
				if (!postPrune && updateGraphWithCoverage(traceDir, tId) < 0) {
					return;
				}
				
				if ( parseSingleTrace(traceDir, tId, new LinkedList<String>(changeSet), localImpactSets) < 0 ) {
					// ignore erroneous or problematic traces
					continue;
				}
				
				// -- DEBUG
				if (debugOut) {
					if (!localImpactSets.isEmpty()) {
						System.out.println("Impact set computed from current trace [no. " + tId + "]:");
						printStatistics(localImpactSets, false);
					}
				}
				
				// merge impact set across all execution traces
				for (String chg : localImpactSets.keySet()) {
					if (impactSets.get(chg) == null) {
						impactSets.put(chg, new LinkedHashSet<String>());
					}
					impactSets.get(chg).addAll(localImpactSets.get(chg));
				}
			}
			catch (FileNotFoundException e) { 
				break;
			}
			catch (IOException e) {
				throw new RuntimeException(e); 
			}
			catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		System.out.println(--tId + " execution traces have been processed.");
		printStatistics(impactSets, true);
	}
	
	private static void printStatistics (Map<String, Set<String>> mis, boolean btitle) {
		if (btitle) {
			System.out.println("\n============ Diver Result ================");
			System.out.println("[Valid Query Set]");
			for (String m:changeSet) {
				System.out.println(m);
			}
		}
		Set<String> aggregatedIS = new LinkedHashSet<String>();
		for (String m : mis.keySet()) {
			System.out.println("[Impact Set of " + m + "]: size= " + mis.get(m).size());
			for (String im : mis.get(m)) {
				System.out.println(im);
			}
			// merge impact sets of all change queries
			aggregatedIS.addAll(mis.get(m));
		}
		if (btitle) {
			System.out.println("\n[Impact Set of All Queries]: size= " + aggregatedIS.size());
			for (String im : aggregatedIS) {
				System.out.println(im);
			}
		}
	}
}

/* vim :set ts=4 tw=4 tws=4 */
