/**
 * File: src/Diver/DiverRun.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai		created; for running the EAS-instrumented subject
 * 07/22/13		hcai		handle InvocationTargetException after invoking the subject entry class;
 *							then the weird issue that EA sequence is not dumped got fixed
 * 11/13/13		hcai		supported two levels of dynamic alias monitoring: method level and method-occurrence level
 *  
*/
package Diver;
import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class DiverRun{
	/*
	 * Genuine EAS will only produce a simplified procedure call sequence that reflects the EA relations;
	 * By default in Diver however this will be not sufficient - we need to produce the full call sequence including all
	 * intermediate method (enter/returned-into) events
	 */
	static boolean EASequenceOnly = false;
	
	static String outputrootDir = "";
	
	public static void main(String args[]){
		if (args.length < 3) {
			System.err.println("Too few arguments: \n\t " +
					"DiverRun subjectName subjectDir binPath [verId] [outputDir] [-Fullseq|-EASeq]\n\n");
			return;
		}
		String subjectName = args[0];

		String subjectDir = args[1]; 
		String binPath = args[2];
		String verId = "";
		if (args.length > 3) {
			verId = args[3];
		}
		
		if (args.length > 4) {
			outputrootDir = args[4];
		}
		
		/** the following two options are expressly set for dynamic alias monitoring */		
		if (args.length > 5) {
			EAMonitor.cachingOIDs = args[5].equalsIgnoreCase("-cachingOIDs");
		}
		
		if (args.length > 6) {
			EAMonitor.instanceLevel = args[6].equalsIgnoreCase("-instanceLevel");
		}
		
		if (args.length > 7) {
			if ( args[7].equalsIgnoreCase("-FullSeq") || args[7].equalsIgnoreCase("-EASeq") ) {
				EASequenceOnly = args[7].equalsIgnoreCase("-EASeq");
			}
		}

		System.out.println("Subject: " + subjectName + " Dir=" + subjectDir + 
				" binpath=" + binPath + " verId=" + verId);
		
		try {
			
			//EAMonitor.setEASequenceOnly(EASequenceOnly);
			EAMonitor.turnDebugOut(false);
			startRunSubject(subjectName, subjectDir, binPath, verId);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void startRunSubject(String name, String dir, String binPath, String verId){
		int n = 0;
		BufferedReader br;
		PrintStream stdout = System.out;
	
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(dir+"/inputs/testinputs.txt")));
			String ts = br.readLine();
			while(ts != null){
				n++;

				String [] args = preProcessArg(ts,dir);
				
				String outputDir;
				if(outputrootDir.equals("")){
					outputDir = dir + "/runs" + "/" + verId;
				}else{
					outputDir = outputrootDir;
				}
				
				File dirF = new File(outputDir);
				if(!dirF.isDirectory())	dirF.mkdirs();
				
				System.setOut(stdout);
				System.out.println("current at test No.  " + n);
					
				// set the name of file as the serialization target of method event maps (F followed by L)
				EAMonitor.setEventMapSerializeFile(outputDir  + "/test"+n+ ".em");

				String outputF = outputDir  + "/test"+n+ ".out";
				String errF = outputDir  + "/test"+n+ ".err";
				
				File outputFile = new File(outputF);
				PrintStream out = new PrintStream(new FileOutputStream(outputFile)); 
				System.setOut(out); 
				
				File errFile = new File(errF);
				PrintStream err = new PrintStream(new FileOutputStream(errFile)); 
				System.setErr(err);
				
				File runSub = new File(binPath);
				URL url = runSub.toURL();
			    URL[] urls = new URL[]{url};
			   
			    try {
			    	/*
					ClassLoader parentloader = new URLClassLoader(urls2);
				    ClassLoader cl = new URLClassLoader( urls, Thread.currentThread().getContextClassLoader() );				    
				    Thread.currentThread().setContextClassLoader(cl);
				    */
			    	ClassLoader cl = new URLClassLoader( urls, ClassLoader.getSystemClassLoader() );
				    Class cls = cl.loadClass(name);
				    
				    Method me=cls.getMethod("main", new Class[]{args.getClass()});
				    me.invoke(null, new Object[]{(Object)args});
				    
				}
			    catch (InvocationTargetException e) {
			    	e.getTargetException().printStackTrace();
			    }
				catch (Exception e) {
					e.printStackTrace();
				}

			   // invoke the "program termination event" for the subject in case there is uncaught exception occurred
			   EAMonitor.terminate("Enforced by DiverRun.");

			   out.flush();
			   out.close();
			   err.close();
			   
			   ts = br.readLine();
			}
			
			br.close();
		} catch (Exception e) {
			e.printStackTrace();
		} 
	}

	public static String[] preProcessArg(String arg,String dir){
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
}

/* vim :set ts=4 tw=4 tws=4 */
