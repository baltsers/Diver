/**
 * File: src/Diver/MultiMethodIA.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 12/25/13		hcai		created; for computing multi-method change impacts by Diver versus EAS; Note
 * 				that this program does not invoke the implementations of Diver and EAS but just parses results
 * 				of single-method change impacts as input
 * 12/28/13		hcai		debugged and verified
 *
*/
package Diver;

import java.io.*;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

public class MultiMethodIA {
	/** the input file giving the single-method CIA results of Diver and EAS */
	protected static String fnSingleMethodResults = "";
	
	/** the set of query method can also be given via a text file */
	protected static String fnQuerylist = "";
	/** the map from query method to its index in the global store */
	protected static Map<String, Integer> query2idx = new LinkedHashMap<String, Integer>();
	protected static Map<Integer, String> idx2query = new LinkedHashMap<Integer, String>();
	
	/** the map from single query to its EAS impact set */
	protected static Map<String, BitSet> singleMethodResultsEAS = new LinkedHashMap<String, BitSet>();
	/** the map from single query to its Diver impact set */
	protected static Map<String, BitSet> singleMethodResultsDiver = new LinkedHashMap<String, BitSet>();
	
	/** the number of repetitions of randomly forming query groups */
	protected static int nReps = 2;
	
	/** keep the default output stream */
	private final static PrintStream stdout = System.out;
	private final static PrintStream stderr = System.err;
	
	/** time cost of EAS and Diver for each query method */
	protected static Long EATime = 0L, DiverTime = 0L;
	
	static int queryGroupSize = 1;
	
	/** the map from category to impact set: 
	 * 0: EAS 
	 * 1: Diver 
	 */
	protected static Map<Integer, Set<String>> finalResult = new LinkedHashMap<Integer, Set<String>>();
	
	/** statistics of all repetitions, each repetition has: 
	 * 		EAS IS size, Diver IS size, FP size, FN size, Diver/EA ratio, EA time, Diver time
	 */
	protected static List<List<Double>> allStats = new ArrayList<List<Double>>();
	
	public static void parseArgs(String args[]){
		assert args.length >= 4;
		fnSingleMethodResults = args[0];
		fnQuerylist = args[1];
		queryGroupSize = Integer.valueOf(args[2]);
		nReps = Integer.valueOf(args[3]);
		System.err.println("input: " + fnSingleMethodResults + " group size=" + queryGroupSize + " repetitions=" + nReps);		
	}
	
	public static void readQueries() {
		BufferedReader br;
		int icnt = 0;
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(fnQuerylist)));
			String ts = br.readLine();
			while(ts != null) {
				idx2query.put(icnt,  ts.trim());
				query2idx.put(ts.trim(), icnt++);
				
				ts = br.readLine();
			}
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void readSingleMethodResults(String startingToken, Map<String, BitSet> singleMethodResults) {
		BufferedReader br;
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(fnSingleMethodResults)));
			String ts = br.readLine();
			String query = "";
			boolean resStart = false;
			int isSize = -1;
			while(ts != null) {
				if (!resStart) {
					int sIdx = ts.indexOf(startingToken);
					if (sIdx!=-1) {
						int endIdx = ts.indexOf(">]", sIdx+1);
						assert endIdx!=-1;
						query = ts.substring(sIdx+startingToken.length()-1, endIdx+1);
						
						int szSIdx = ts.indexOf("size=", endIdx+1);
						assert szSIdx!=-1;
						isSize = Integer.valueOf(ts.substring(szSIdx+5, ts.indexOf(" ", szSIdx+6)));
						resStart = true;
						continue;
					}
					ts = br.readLine();
					continue;
				}
				for (int icnt=0; icnt < isSize; ++icnt) {
					ts = br.readLine();
					assert ts != null;
					singleMethodResults.get(query).set(query2idx.get(ts.trim()));
				}
				resStart = false;
				query="";
				isSize = -1;
				ts = br.readLine();
			}
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String args[]){
		if (args.length < 4) {
			System.err.println("too few arguments.");
			return;
		}
		parseArgs(args);
		
		if (fnQuerylist.length()<1) {
			System.err.println("invalid query list from " + fnQuerylist);
			return;
		}
		else {
			readQueries();
		}
		if (query2idx.size() < 1) {
			System.err.println("invalid query list.");
			return;
		}
		
		for (String query : query2idx.keySet()) {
			singleMethodResultsEAS.put(query, new BitSet(query2idx.keySet().size()));
			singleMethodResultsDiver.put(query, new BitSet(query2idx.keySet().size()));
		}

		if (fnSingleMethodResults.length()<1) {
			System.err.println("invalid single method query result input from " + fnSingleMethodResults);
			return;
		}
		else {
			readSingleMethodResults("==== EAS impact set of [<", singleMethodResultsEAS);
			readSingleMethodResults("==== Diver impact set of [<", singleMethodResultsDiver);
		}
		
		if (queryGroupSize <= 1) {
			System.err.println("Nothing to do with group size <= 1.");
		}
		else if (queryGroupSize > 1) {
			for (int j = 0; j < nReps; ++j) {
				System.out.println("\t\t=============== Repetition " + j + " ================\t\t");
				multipleMethodQuery();
			}
		}
		
		// compute the overall statistics
		Double szEAISavg=.0, szDiverISavg=.0, szFPavg=.0, szFNavg=.0, DERatioavg=.0, tEAavg=.0, tDiveravg=.0;
		int nSamples = allStats.size();
		for (int k = 0; k < nSamples; ++k) {
			szEAISavg += allStats.get(k).get(0);
			szDiverISavg += allStats.get(k).get(1);
			szFPavg += allStats.get(k).get(2);
			szFNavg += allStats.get(k).get(3);
			DERatioavg += allStats.get(k).get(4);
			tEAavg += allStats.get(k).get(5);
			tDiveravg += allStats.get(k).get(6);
		}
		
		szEAISavg /= nSamples;
		szDiverISavg /= nSamples;
		szFPavg  /= nSamples;
		szFNavg  /= nSamples;
		DERatioavg  /= nSamples;
		tEAavg /= nSamples;
		tDiveravg  /= nSamples;
		
		Double szEAISstd=.0, szDiverISstd=.0, szFPstd=.0, szFNstd=.0, DERatiostd=.0, tEAstd=.0, tDiverstd=.0;
		for (int k = 0; k < nSamples; ++k) {
			szEAISstd += (allStats.get(k).get(0)-szEAISavg)*(allStats.get(k).get(0)-szEAISavg);
			szDiverISstd += (allStats.get(k).get(1)-szDiverISavg)*(allStats.get(k).get(1)-szDiverISavg);
			szFPstd += (allStats.get(k).get(2)-szFPavg)*(allStats.get(k).get(2)-szFPavg);
			szFNstd += (allStats.get(k).get(3)-szFNavg)*(allStats.get(k).get(3)-szFNavg);
			DERatiostd += (allStats.get(k).get(4)-DERatioavg)*(allStats.get(k).get(4)-DERatioavg);
			tEAstd += (allStats.get(k).get(5)-tEAavg)*(allStats.get(k).get(5)-tEAavg);
			tDiverstd += (allStats.get(k).get(6)-tDiveravg)*(allStats.get(k).get(6)-tDiveravg);
		}
		
		szEAISstd=Math.sqrt(szEAISstd/nSamples);
		szDiverISstd=Math.sqrt(szDiverISstd/nSamples);
		szFPstd=Math.sqrt(szFPstd/nSamples);
		szFNstd=Math.sqrt(szFNstd/nSamples);
		DERatiostd=Math.sqrt(DERatiostd/nSamples);
		tEAstd=Math.sqrt(tEAstd/nSamples);
		tDiverstd=Math.sqrt(tDiverstd/nSamples);
	
		System.out.println("\t\t=============== FINAL RESULTS ================\t\t");
		DecimalFormat df = new DecimalFormat("#.####");
		
		System.out.println("average\t"+df.format(szEAISavg)+"\t"+df.format(szDiverISavg)+"\t"+df.format(szFPavg)+
				"\t"+df.format(szFNavg)+"\t"+df.format(DERatioavg)+"\t"+df.format(tEAavg)+"\t"+df.format(tDiveravg));
		System.out.println("stdev\t"+df.format(szEAISstd)+"\t"+df.format(szDiverISstd)+"\t"+df.format(szFPstd)+
				"\t"+df.format(szFNstd)+"\t"+df.format(DERatiostd)+"\t"+df.format(tEAstd)+"\t"+df.format(tDiverstd));
	}
	
	public static void multipleMethodQuery() {
		int i = query2idx.keySet().size(), tn=0;
		List<String> querystore = new ArrayList<String>(query2idx.keySet());
		Random r = new Random(System.currentTimeMillis());
		int gcnt = 1;
		while (i > 0) {
			Set<String> curgrp = new LinkedHashSet<String>();
			
			int n = 0;
			while (!querystore.isEmpty() && n < queryGroupSize) {
				String m = querystore.get(r.nextInt(i));
				curgrp.add(m);
				i--; n++;
				querystore.remove(m);
			}
			tn += n;
			System.err.println("====== current at the " + gcnt + "/" + Math.ceil(query2idx.keySet().size()*1.0/queryGroupSize) + 
					" query group, now there are [" + i + "/" + query2idx.keySet().size() + "] queries to go ======");
			try {
				finalResult.clear();
				EATime = DiverTime = 0L;
				startRunSubject(curgrp, gcnt);
				gcnt++;
			}
			catch (Throwable t) {
				System.setErr(stderr);
				System.err.println("ERROR occurred during the runtime phase!");
				t.printStackTrace(stderr);
			}
			finally {
				System.setErr(stderr);
				System.setOut(stdout);
			}
		}
		System.err.println("Totally " + tn + "/" + query2idx.keySet().size() + " methods have been queried on EAS and Diver.");
	}
		
	public static void startRunSubject(String queryMethod, int counter) {
		Set<String> queries = new LinkedHashSet<String>();
		queries.add(queryMethod);
		startRunSubject(queries, counter);
	}
	public static void startRunSubject(Set<String> queries, int counter) {	
		
		// initialize the final result map
		for (Integer cat = 0; cat < 2; cat++) {
			finalResult.put(cat, new LinkedHashSet<String>());
		}

		//////////////////////////////// Compute EAS impact set //////////////////////////////////////////////
		System.setErr(stderr);
		System.err.println("Computing EAS impact set ......  ");
		long EASTime = System.currentTimeMillis();
		Set<String> EAIS = new LinkedHashSet<String>();
		BitSet eaRes = new BitSet(query2idx.keySet().size());
		for (String query:queries) {
			assert singleMethodResultsEAS.containsKey(query);
			eaRes.or(singleMethodResultsEAS.get(query));
		}
		for (int idx = 0; idx < query2idx.keySet().size(); ++idx) {
			if (eaRes.get(idx)) {
				EAIS.add(idx2query.get(idx));
			}
		}
		EATime += System.currentTimeMillis() - EASTime;
								
		//////////////////////////////// Compute Diver impact set //////////////////////////////////////////////
		System.setErr(stderr);
		System.err.println("Computing Diver impact set ......  ");
		long DiverSTime = System.currentTimeMillis();
		Set<String> DiverIS = new LinkedHashSet<String>();
		BitSet diverRes = new BitSet(query2idx.keySet().size());
		for (String query:queries) {
			assert singleMethodResultsDiver.containsKey(query);
			diverRes.or(singleMethodResultsDiver.get(query));
		}
		for (int idx = 0; idx < query2idx.keySet().size(); ++idx) {
			if (diverRes.get(idx)) {
				DiverIS.add(idx2query.get(idx));
			}
		}
		
		DiverTime += System.currentTimeMillis() - DiverSTime;
										
		//////////////////////////////// merge result  //////////////////////////////////////////////
		finalResult.get(0).addAll(EAIS);
		finalResult.get(1).addAll(DiverIS);
						
		dumpStatistics(queries, stdout,stderr);
	}
	
	/** dump impact sets of EAS versus mDEA for the specific mutation point in the given query method */ 
	public static void dumpStatistics(Set<String> queries, PrintStream os, PrintStream or) {
		if (finalResult.get(0).size() < 1) {
			// if this query method is not covered by any of the nTests tests, nothing to be reported
			return;
		}
		
		String allqueries = "";
		int istr = 0;
		for (String queryMethod : queries) {
			istr ++;
			if (istr > 1) allqueries += "\n";
			allqueries += queryMethod;
		}
		
		// dump complete data
		or.println("==== EAS impact set of [" + allqueries +"]  size=" + finalResult.get(0).size() + " ===");
		for (String m : finalResult.get(0)) {
			or.println(m);
		}
		
		or.println("==== Diver impact set of [" + allqueries +"]  size=" + finalResult.get(1).size() + " ====");
		for (String m : finalResult.get(1)) {
			or.println(m);
		}
		
		// compute FPs and FNs (take DiverImpactSet as the ground truth: FP=EAIS-DiverIS, FN=DiverIS-EAIS)
		Set<String> IntersectionAll = new LinkedHashSet<String>(finalResult.get(0)); 
		IntersectionAll.retainAll(finalResult.get(1));
		Set<String> FPAll = new LinkedHashSet<String>(finalResult.get(0));
		FPAll.removeAll(finalResult.get(1));
		Set<String> FNAll = new LinkedHashSet<String>(finalResult.get(1));
		FNAll.removeAll(finalResult.get(0));
		
		or.println("==== EASIS - DiverIS  size=" + FPAll.size() + " ====");
		for (String m : FPAll) {
			or.println(m);
		}
		or.println("==== DiverIS - EASIS  size=" + FNAll.size() + " ====");
		for (String m : FNAll) {
			or.println(m);
		}
		or.println();
		or.flush();
		
		DecimalFormat df = new DecimalFormat("#.####");
		
		// compute statistics and dump
		String title = queries + "\t";
		
		double DESizeRatio = finalResult.get(0).size()<1?1.0:finalResult.get(1).size()*1.0 / finalResult.get(0).size();
		double EDTimeRatio = DiverTime<1?1.0:EATime*1.0 / DiverTime;
		
		os.print(title);
		os.print(finalResult.get(0).size() + "\t" + finalResult.get(1).size() + "\t" + FPAll.size() + "\t" +
				FNAll.size() + "\t" + df.format(DESizeRatio) + "\t" + EATime + "\t" + DiverTime + "\t" + 
				df.format(EDTimeRatio) + "\n");
		
		os.println();
		os.flush();
		
		List<Double> curStat = new ArrayList<Double>();
		curStat.add(finalResult.get(0).size()*1.0);
		curStat.add(finalResult.get(1).size()*1.0);
		curStat.add(FPAll.size()*1.0);
		curStat.add(FNAll.size()*1.0);
		curStat.add(DESizeRatio);
		curStat.add(EATime*1.0);
		curStat.add(DiverTime*1.0);
		
		allStats.add(curStat);
	}

} // MultiMethodIA

/* vim :set ts=4 tw=4 tws=4 */
