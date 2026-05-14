/**
 * File: src/Diver/RunAnalysis.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 10/18/13		hcai		created; for running both EAS and Diver on a set of queries in a single process/memory space
 * 10/21/13		hcai		run EAS and Diver only once and then query all methods requested, instead of running both
 *							CIAs for each query
 * 10/23/13		hcai		added "noRun" option for excluding the runtime phase
 * 10/29/13		hcai		applied the "runtime statement coverage pruning" for Diver
 * 11/03/13		hcai		important fix: reInitialize (by updateGraphWithCoverage) dynamic MDG with coverage 
 *							data per test case before obtainValidChangeSet instead of after that
 * 11/15/13		hcai		supported two levels of dynamic alias monitoring: method level and method-occurrence level
 * 11/18/13		hcai		added option for combining statement coverage with dynamic alias data (on method instance level) for impact computation
 * 11/22/13		hcai		further extended for combining statement coverage with dynamic alias data (on method level) for impact computation
 * 12/11/13		hcai		added supports for querying impacts of multi-method changes
 * 04/05/14		hcai		generalized inputs handling to adopt to the use of this class by the Repository-change Diver/EAS experiment pipeline 
 *
*/
package Diver;

import java.io.*;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class RunAnalysis {
	// the necessary location arguments that give the running subjects */
	/** the subject location and version-seed suffix, with which the class paths, inputs and output dirs are to 
	 * be derived according to the naming routines 
	 */
	protected static String SubjectDir = "";
	protected static String VersionSeed = "";
	/** the entry class name */
	protected static String entryClsName = "";
	/** the set of query method to be sent to EAS and Diver */
	protected static Set<String> queryMethods = new LinkedHashSet<String>();
	/** the set of query method can also be given via a text file */
	protected static String fnQuerylist = "";
			
	// the following parameters are to be reduced from the above according to the naming routines */
	/** the class path for the EA instrumented subject */
	protected static String EABinPath="";
	/** the output path for the EA instrumented subject */
	protected static String EAOutputPath="";
	/** the class path for the Diver instrumented subject */
	protected static String DiverBinPath="";
	/** the output path for the Diver instrumented subject */
	protected static String DiverOutputPath="";
	
	/** the input text that indexes all test cases */
	protected static String testInputFile ="";
	/** the number of tests to execute */
	protected static int	nTests = 0;
	
	/** if remove output files after each test got executed */
	public static boolean keepOutputs = true;
	
	/** keep the default output stream */
	private final static PrintStream stdout = System.out;
	private final static PrintStream stderr = System.err;
	
	/** to avoid getting stuck on some test execution, 
	 * we limit the maximal length of time for each, in minutes */
	protected static long MAXTESTDURATION = 30L;
	
	/** total number of skipped tests found not covering the query method according EAS full trace */
	protected static Integer totalSkippedTests = 0;
	
	/** time cost of EAS and Diver for each query method */
	protected static Long EATime = 0L, DiverTime = 0L;
	
	/** if include the runtime phase in this process or not */
	protected static boolean needRun = false;
	
	/** if applying runtime statement coverage information to prune statements not executed, examined per test case */
	static boolean applyStatementCoverage = false;
	/** prune non-covered/non-aliased nodes and edges prior to or after basic querying process: 
	 * both are equivalent in terms of eventual impact set but can be disparate in performance
	 */
	public static boolean postPrune = true;
	
	/** if applying runtime object alias checking to prune heap value edges on which the source 
	 * and target nodes are not dynamically aliased 
	 */
	static boolean applyDynAliasChecking = false;
	/** if pruning based on the dynamic alias information at the method instance level, or just the method level */
	public static boolean instancePrune = true;
	
	static int queryGroupSize = 1;
	
	/** the map from category to impact set: 
	 * 0: EAS 
	 * 1: Diver 
	 */
	protected static Map<Integer, Set<String>> finalResult = new LinkedHashMap<Integer, Set<String>>();
	
	public static void parseArgs(String args[]){
		assert args.length >= 5;
		SubjectDir = args[0];
		VersionSeed = args[1];
		entryClsName = args[2];
		fnQuerylist = args[3];
		nTests = Integer.valueOf(args[4]);
		System.err.println("Subject: " + SubjectDir + " ver-seed=" + VersionSeed +
				" boostrap class=" + entryClsName + " number of tests=" + nTests);
		
		/** make this class more general for other uses where VersionSeed is not required (particulary for repository revisions) */
		/*
		EABinPath = SubjectDir + File.separator + "EAInstrumented-" + VersionSeed;
		EAOutputPath = SubjectDir + File.separator + "EAoutdyn-" + VersionSeed;
		DiverBinPath = SubjectDir + File.separator + "DiverInstrumented-" + VersionSeed;
		DiverOutputPath = SubjectDir + File.separator + "Diveroutdyn-" + VersionSeed;
		*/
		EABinPath = SubjectDir + File.separator + "EAInstrumented" + ((VersionSeed.length()>=1)?("-"+VersionSeed):"");
		EAOutputPath = SubjectDir + File.separator + "EAoutdyn" + ((VersionSeed.length()>=1)?("-"+VersionSeed):"");
		DiverBinPath = SubjectDir + File.separator + "DiverInstrumented" + ((VersionSeed.length()>=1)?("-"+VersionSeed):"");
		DiverOutputPath = SubjectDir + File.separator + "Diveroutdyn" + ((VersionSeed.length()>=1)?("-"+VersionSeed):"");
				
		testInputFile = SubjectDir + File.separator + "inputs" + File.separator + "testinputs.txt";
		
		if (args.length >= 6) {
			applyStatementCoverage = args[5].equalsIgnoreCase("-stmtcov");
			applyDynAliasChecking = args[5].equalsIgnoreCase("-dynalias");
		}
		if (args.length >= 7) {
			postPrune = args[6].equalsIgnoreCase("-postprune"); // secondary option working with only "-stmtcov"
			instancePrune = args[6].equalsIgnoreCase("-instanceprune"); // secondary option working with only "-dynalias"
		}
		// apply both statement coverage and dynamic alias data, using the best secondary options (postprune and instanceprune respectively) for each
		if (args.length >= 6 && args[5].equalsIgnoreCase("-stmtcovdynalias")) {
			applyStatementCoverage = applyDynAliasChecking = true;
			postPrune /*= instancePrune*/ = true;
		}
		
		if (args.length >= 8) {
			if (Character.isDigit(args[7].charAt(0))) {
				queryGroupSize = Integer.valueOf(args[7]);
			}
			else {
				needRun = args[7].equalsIgnoreCase("-needRun");
			}
		}
		if (args.length >= 9) {
			long MaxTestDuration = Long.valueOf(args[8]);
			MAXTESTDURATION = MaxTestDuration;
		}
	}
	
	public static void readQueries() {
		BufferedReader br;
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(fnQuerylist)));
			String ts = br.readLine();
			while(ts != null) {
				queryMethods.add(ts.trim());
				
				ts = br.readLine();
			}
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String args[]){
		if (args.length < 5) {
			System.err.println("too few arguments.");
			return;
		}
		parseArgs(args);
		
		DiverAnalysis.applyStatementCoverage = applyStatementCoverage;
		DiverAnalysis.postPrune = postPrune;
		DiverAnalysis.applyDynAliasChecking = applyDynAliasChecking;
		DiverAnalysis.instancePrune = instancePrune;
		
		if (fnQuerylist.length()<1) {
			File queryF = new File(EABinPath + File.separator + "functionList.out");
			if (queryF.exists()) {
				fnQuerylist = queryF.getAbsolutePath();
				readQueries();
			}
			else {
				System.err.println("invalid query list.");
				return;
			}
		}
		else {
			readQueries();
		}
		if (queryMethods.size() < 1) {
			System.err.println("invalid query list.");
			return;
		}
		
		// one of the primary reason for the creation of this particular runner is to save the redundant time cost of loading the static MDG
		if (Diver.DiverAnalysis.init(DiverBinPath) != 0) {
			return;
		}
		
		if (queryGroupSize == 1) {
			singleMethodQuery();
		}
		else if (queryGroupSize > 1) {
			multipleMethodQuery();
		}
	}
	
	public static void multipleMethodQuery() {
		int i = queryMethods.size(), tn=0;
		List<String> querystore = new ArrayList<String>(queryMethods);
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
			System.err.println("====== current at the " + gcnt + "/" + Math.ceil(queryMethods.size()*1.0/queryGroupSize) + 
					" query group, now there are [" + i + "/" + queryMethods.size() + "] queries to go ======");
			try {
				finalResult.clear();
				totalSkippedTests = 0;
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
		System.err.println("Totally " + tn + "/" + queryMethods.size() + " methods have been queried on EAS and Diver.");
	}
	
	public static void singleMethodQuery() {
		int i = 1;
		for (String queryMethod : queryMethods) {
			System.err.println("====== current at the query [" + i + "/" + queryMethods.size() + "] " + queryMethod + " ======");
			try {
				finalResult.clear();
				totalSkippedTests = 0;
				EATime = DiverTime = 0L;
				startRunSubject(queryMethod, i);
				i++;
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
		System.err.println("Totally " + i + "/" + queryMethods.size() + " methods have been queried on EAS and Diver.");
	}
		
	public static void startRunSubject(String queryMethod, int counter) {
		Set<String> queries = new LinkedHashSet<String>();
		queries.add(queryMethod);
		startRunSubject(queries, counter);
	}
	public static void startRunSubject(Set<String> queries, int counter) {	
		String EAoutputDir = EAOutputPath + File.separator;
		String DiveroutputDir = DiverOutputPath + File.separator;
		
		File dirEAF = new File(EAoutputDir);
		if(!dirEAF.isDirectory())	dirEAF.mkdirs();
		File dirDiverF = new File(DiveroutputDir);
		if(!dirDiverF.isDirectory())	dirDiverF.mkdirs();
		
		int n = 0;
		BufferedReader br = null;
		
		// initialize the final result map
		for (Integer cat = 0; cat < 2; cat++) {
			finalResult.put(cat, new LinkedHashSet<String>());
		}
		
		List<String> Chglist = new ArrayList<String>();
		Chglist.addAll(queries);
	
		try {
			FileInputStream fin = null;
			String ts = null;
			if (needRun && counter <=1) {
				fin = new FileInputStream(testInputFile);
				br = new BufferedReader(new InputStreamReader(fin));
				ts = br.readLine();
			}
			while( (ts != null || !needRun || counter >1) && n < nTests){
				n++;
				final String[] args = preProcessArg(ts,SubjectDir);
				
				//System.setOut(stdout);
				//System.out.println("test:  " + args[0] + " " + args[1]);
				System.setErr(stderr);
				System.err.println("For EAS current at the test No.  " + n);				
				if (needRun && counter <= 1) {
					//////////////////////////////// Run EA instrumented subject //////////////////////////////////////////////
					final String outputEAF = EAoutputDir + "test" + n + ".out";
					final String errEAF = EAoutputDir + "test" + n + ".err";
					
					// redirect stdout and stderr 
					final File outputFileEA = new File(outputEAF);
					final PrintStream outEA = new PrintStream(new FileOutputStream(outputFileEA)); 
					System.setOut(outEA); 
					final File errFileEA = new File(errEAF);
					final PrintStream errEA = new PrintStream(new FileOutputStream(errFileEA)); 
					System.setErr(errEA);
					
					// set the name of file as the serialization target of method event maps (F followed by L)
					EAS.Monitor.setEventMapSerializeFile(EAoutputDir  + "test"+n+ ".em");
					
					final File runSubEA = new File(EABinPath);
					@SuppressWarnings("deprecation")
					final URL urlEA = runSubEA.toURL();
				    final URL[] urlsEA = new URL[]{urlEA};
				    
				    ExecutorService EAservice = Executors.newSingleThreadExecutor();
				    try {
				        Runnable EARunner = new Runnable() {
					@Override public void run() {
					
					try {
					    ClassLoader clEA = new URLClassLoader( urlsEA, Thread.currentThread().getContextClassLoader() );
					    Thread.currentThread().setContextClassLoader(clEA);
					    
					    Class<?> clsEA = clEA.loadClass(entryClsName);
					    
					    Method meEA=clsEA.getMethod("main", new Class[]{args.getClass()});
	
					    meEA.invoke(null, new Object[]{(Object)args});
					}
					catch (Exception e) {
						e.printStackTrace();
					}
					
					outEA.flush();
					outEA.close();
					errEA.flush();
					errEA.close();
					
					}};
					Future<?>  EAfuture = EAservice.submit(EARunner);
					EAfuture.get(MAXTESTDURATION*60, TimeUnit.SECONDS);
				    }
				    catch (final InterruptedException e) {
				        // The thread was interrupted during sleep, wait or join
				    	System.setErr(stderr);
						System.err.println("Running EAS at the test No.  " + n + " thread interrupted.");
						EAS.Monitor.terminate("Enforced by EARun.");
						ts = br.readLine();
						continue;
				    }
				    catch (final TimeoutException e) {
				        // Took too long!
				    	System.setErr(stderr);
						System.err.println("Running EAS at the test No.  " + n + " TimeOut after " + MAXTESTDURATION*60 + " seconds");
						EAS.Monitor.terminate("Enforced by EARun.");
						ts = br.readLine();
						continue;
				    }
				    catch (final ExecutionException e) {
				        // An exception from within the Runnable task
				    	System.setErr(stderr);
						System.err.println("Running EAS at the test No.  " + n + " exception thrown during test execution");
						EAS.Monitor.terminate("Enforced by EARun.");
						ts = br.readLine();
						continue;
				    }
				    finally {
				        EAservice.shutdown();
				    }
				    
				    // invoke the "program termination event" for the subject in case there is uncaught exception occurred
				    EAS.Monitor.terminate("Enforced by EARun.");
				}
				
				//////////////////////////////// Compute EAS impact set //////////////////////////////////////////////
				System.setErr(stderr);
				System.err.println("Computing EAS impact set ......  ");
				long EASTime = System.currentTimeMillis();
				Set<String> EAIS = new LinkedHashSet<String>();
				int szEAIS = EAS.EAAnalysis.parseSingleTrace(EAoutputDir, n, Chglist, EAIS);
				/*
				if (!keepOutputs) {
					deleteFile(outputEAF);
					deleteFile(errEAF);
				}
				*/
				if ( (!needRun || counter > 1) && szEAIS<1) {
					// this test did not cover the query method, no point to run with Diver because the mutation point is within the method
					System.err.println("Non-covering test skipped ......  ");
					totalSkippedTests ++;
					if (needRun && counter <= 1) {
						ts = br.readLine();
					}
					continue;
				}
				EATime += System.currentTimeMillis() - EASTime;
				
				//////////////////////////////// Run Diver instrumented subject //////////////////////////////////////////////
				System.setErr(stderr);
				System.err.println("For Diver current at the test No.  " + n);
				if (needRun && counter <= 1) {
					final String outputDiverF = DiveroutputDir + "test" + n + ".out";
					final String errDiverF = DiveroutputDir + "test" + n + ".err";
					
					// redirect stdout and stderr 
					final File outputFileDiver = new File(outputDiverF);
					final PrintStream outDiver = new PrintStream(new FileOutputStream(outputFileDiver)); 
					System.setOut(outDiver); 
					final File errFileDiver = new File(errDiverF);
					final PrintStream errDiver = new PrintStream(new FileOutputStream(errFileDiver)); 
					System.setErr(errDiver);
					
					// set the name of file as the serialization target of method event maps (full trace)
					Diver.EAMonitor.setEventMapSerializeFile(DiveroutputDir  + "test"+n+ ".em");
					
					final File runSubDiver = new File(DiverBinPath);
					@SuppressWarnings("deprecation")
					final URL urlDiver = runSubDiver.toURL();        
					final URL[] urlsDiver = new URL[]{urlDiver};
					
				    ExecutorService Diverservice = Executors.newSingleThreadExecutor();
				    try {
				        Runnable DiverRunner = new Runnable() {
					@Override public void run() {
									
					try {
						ClassLoader clDiver = new URLClassLoader( urlsDiver, Thread.currentThread().getContextClassLoader() );
						Thread.currentThread().setContextClassLoader(clDiver);
						    
					    Class<?> clsDiver = clDiver.loadClass(entryClsName);
					    
					    Method meDiver=clsDiver.getMethod("main", new Class[]{args.getClass()});
	
					    meDiver.invoke(null, new Object[]{(Object)args});
					}
					catch (Exception e) {
						e.printStackTrace();
					}
					
					outDiver.flush();
					outDiver.close();
					errDiver.flush();
					errDiver.close();
					
					}};
					Future<?>  Diverfuture = Diverservice.submit(DiverRunner);
					Diverfuture.get(MAXTESTDURATION*60*10, TimeUnit.SECONDS); // mDEA is expected to take longer to run than EAS
				    }
				    catch (final InterruptedException e) {
				        // The thread was interrupted during sleep, wait or join
				    	System.setErr(stderr);
						System.err.println("Running Diver at the test No.  " + n + " thread interrupted.");
						ts = br.readLine();
						continue;
				    }
				    catch (final TimeoutException e) {
				        // Took too long!
				    	System.setErr(stderr);
						System.err.println("Running Diver at the test No.  " + n + " TimeOut after " + MAXTESTDURATION*60*10 + " seconds");
						ts = br.readLine();
						continue;
				    }
				    catch (final ExecutionException e) {
				        // An exception from within the Runnable task
				    	System.setErr(stderr);
						System.err.println("Running Diver at the test No.  " + n + " exception thrown during test execution");
						ts = br.readLine();
						continue;
				    }
				    finally {
				        Diverservice.shutdown();
				    }
				}
				
				//////////////////////////////// Compute Diver impact set //////////////////////////////////////////////
				System.setErr(stderr);
				System.err.println("Computing Diver impact set ......  ");
				
				if (!Diver.DiverAnalysis.postPrune && Diver.DiverAnalysis.updateGraphWithCoverage(DiveroutputDir, n) < 0) {
					System.err.println("Error reading coverage information with test No. " + n);
					if (needRun && counter <= 1) {
						ts = br.readLine();
					}
					continue;
				}
				Map<String, Set<String>> localImpactSets = new LinkedHashMap<String, Set<String>>();
				String allqueries = "";
				int istr = 0;
				for (String queryMethod : queries) {
					localImpactSets.put(queryMethod, new LinkedHashSet<String>());
					istr++;
					if (istr > 1) allqueries += ";";
					allqueries += queryMethod;
				}
				int dqret = Diver.DiverAnalysis.obtainValidChangeSet(allqueries);
				long DiverSTime = System.currentTimeMillis();
				if (dqret >= 1) {
					dqret = Diver.DiverAnalysis.parseSingleTrace(DiveroutputDir, n, new ArrayList<String>(Diver.DiverAnalysis.getChangeSet()), localImpactSets);
				}
				else {
					System.err.println("Invalid query: " + allqueries + " actual querying skipped.");
				}
				DiverTime += System.currentTimeMillis() - DiverSTime;
				if ( dqret < 0) {
					System.err.println("Error occurred in Diver impact set querying with test No. " + n);
					if (needRun && counter <= 1) {
						ts = br.readLine();
					}
					continue;
				}
				/*
				if (!keepOutputs) {
					deleteFile(outputDiverF);
					deleteFile(errDiverF);
				}
				*/
								
				//////////////////////////////// merge result  //////////////////////////////////////////////
				finalResult.get(0).addAll(EAIS);
				for (String queryMethod : queries) {
					finalResult.get(1).addAll(localImpactSets.get(queryMethod));
				}
				
				// next test case
				if (needRun && counter <= 1) {
					ts = br.readLine();
				}
			}
			
			if (needRun && counter <= 1) {
				fin.close();
				br.close();
			}
		} catch (Exception e) {
			System.setOut(stdout);
			e.printStackTrace();
			//return;
		}
		finally {
			dumpStatistics(queries, stdout,stderr);
		}
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
		
		os.println("==== valid versus non-covering tests [" + (nTests-totalSkippedTests) +" : " + totalSkippedTests + "] ====");
		// compute statistics and dump
		String title = VersionSeed + "\t" + queries + "\t";
		
		double DESizeRatio = finalResult.get(0).size()<1?1.0:finalResult.get(1).size()*1.0 / finalResult.get(0).size();
		double EDTimeRatio = DiverTime<1?1.0:EATime*1.0 / DiverTime;
		
		os.print(title);
		os.print(finalResult.get(0).size() + "\t" + finalResult.get(1).size() + "\t" + FPAll.size() + "\t" +
				FNAll.size() + "\t" + df.format(DESizeRatio) + "\t" + EATime + "\t" + DiverTime + "\t" + 
				df.format(EDTimeRatio) + "\n");
		
		os.println();
		os.flush();
	}

	public static String[] preProcessArg(String arg, String dir) {
		if (arg == null) return null;
		String s1 = arg.replaceAll("\\\\+","/").replaceAll("\\s+", " ");
 
		if(s1.startsWith(" "))
			s1 = s1.substring(1,s1.length());
		String argArray[] =  s1.split(" ");
		for(int i=0;i<argArray.length;i++){
			if(argArray[i].startsWith("..")){
				argArray[i] = argArray[i].replaceFirst("..", dir);
			}
		}		
		return argArray;
	}
	
	public static int deleteFile(String fname) {
		File fObj = new File(fname);
		try {
			if (fObj.exists() && fObj.isFile()) {
				fObj.delete();
			}
		} 
		catch (SecurityException e) { System.err.println("Couldn't delete file due to security reasons: " + fObj + e); return -2;}
		catch (Throwable e) { System.err.println("Couldn't delete file due to unexpected reason: " + fObj + e); return -1;}
		return 0;
	}
} // RunAnalysis

/* vim :set ts=4 tw=4 tws=4 */
