/**
 * File: src/EAS/EARun.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 05/20/13		hcai		created; for running the EAS-instrumented subject
 * 05/21/13		hcai		add "EASequenceOnly" option control at runtime; 
 *							fix output directory bugs
 * 05/23/13		hcai		fix the argument processing bug for "-fullseq"/"-easeq" option
 * 05/27/13		hcai		enforce monitor terminate invocation to ensure the event sequence can output;
 *							restrictly there is no way to guarantee this invocation by inserting program END probe
 *							(consider the entry method got an uncaught exception.)
 * 10/09/13		hcai		add optional dumping of dynamic call map
 *  
*/
package EAS;
import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class EARun{
	/*
	 * Genuine EAS will only produce a simplified procedure call sequence that reflects the EA relations;
	 * By default this will be compiled. Otherwise if specified to produce the full call sequence including all
	 * intermediate method (enter/returned-into) events
	 */
	static boolean EASequenceOnly = true;
	
	/* if dump call map at the end of execution of each test */
	static boolean dumpCallmap = false;
	
	static String outputrootDir = "";
	
	/** map from test to corresponding expected full EAS trace length */
	protected static Map<String, Integer> test2tracelen = new LinkedHashMap<String, Integer>();
	
	public static void main(String args[]){
		if (args.length < 3) {
			System.err.println("Too few arguments: \n\t " +
					"EARun subjectName subjectDir binPath [verId] [outputDir] [-Fullseq|-EASeq]\n\n");
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
		
		if (args.length > 5) {
			dumpCallmap = args[5].equalsIgnoreCase("-callmap");
		}
		
		if (args.length > 6) {
			if ( args[6].equalsIgnoreCase("-FullSeq") || args[6].equalsIgnoreCase("-EASeq") ) {
				EASequenceOnly = args[6].equalsIgnoreCase("-EASeq");
			}
		}

		System.out.println("Subject: " + subjectName + " Dir=" + subjectDir + 
				" binpath=" + binPath + " verId=" + verId);
		
		try {
			
			Monitor.setEASequenceOnly(EASequenceOnly);
			Monitor.setDumpCallmap(dumpCallmap);
			startRunSubject(subjectName, subjectDir, binPath, verId);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		dumpTracelengths(outputrootDir + "/traceLengths.txt");
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
				Monitor.setEventMapSerializeFile(outputDir  + "/test"+n+ ".em");
				
				// set the name of file as the serialization target of method call maps
				Monitor.setCallMapSerializeFile(outputDir  + "/test"+n+ ".cm");
				
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
			    	//ClassLoader cl = new URLClassLoader( urls ); 
				    ClassLoader cl = new URLClassLoader( urls, Thread.currentThread().getContextClassLoader() );
				    Thread.currentThread().setContextClassLoader(cl);
			    	
				    Class cls = cl.loadClass(name);
				    Method me=cls.getMethod("main", new Class[]{args.getClass()});
				    me.invoke(null, new Object[]{(Object)args});
				    */
			    	
				    //Class<?> cls = Class.forName(clsname, true, new HPClassLoader( clsname ));
			    	// *ClassLoader cl = new URLClassLoader( urls, ClassLoader.getSystemClassLoader() );
			    	// *Class<?> cls = Class.forName(clsname, true, cl);
				    //Object instance = cls.newInstance();
				    // *Method me = cls.getMethod("main", new Class[]{args.getClass()});
				    // *me.invoke(null/*instance*/, new Object[]{(Object)args});
				    
				    /*
				    Thread.currentThread().getContextClassLoader().clearAssertionStatus();
				    ClassLoader.getSystemClassLoader().clearAssertionStatus();
				    cl.clearAssertionStatus();
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
			   Monitor.terminate("Enforced by EARun.");

			   out.flush();
			   out.close();
			   err.close();
			   
			   /** save full trace length */
			   test2tracelen.put("test"+n, Monitor.getFullTraceLength());
			   
			   ts = br.readLine();
			}
			
			br.close();
		} catch (Exception e) {
			e.printStackTrace();
		} 
	}
	
	public static void dumpTracelengths(String fn) {
		File fObj = new File(fn);
		try {
			BufferedWriter writer = new BufferedWriter(new FileWriter(fObj));
			
			for (Map.Entry<String, Integer> en : test2tracelen.entrySet()) {
				writer.write(en.getKey() + "\t" + en.getValue() +"\n");
			}
			writer.flush();
			writer.close();
		}
		catch (FileNotFoundException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (SecurityException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (IOException e) { System.err.println("Couldn't write file: " + fObj + e); }
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
