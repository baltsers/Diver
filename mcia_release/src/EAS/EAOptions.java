/**
 * File: src/EAS/EAOptions.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 05/17/13		hcai		created; for command-line argument processing for EAS Instrumenter
 * 05/21/13		hcai		add option "dumpJimple" for debugging purposes
 * 05/24/13		hcai		add option "sclinit" to probe for initializing the monitor in 
 *							the possibly present <clinit> to strictly follow the semantics of
 *							program start event; Note subject instrumented with this option enabled
 *							MUST be run independently as opposed to running by EARun
 * 07/04/13		hcai		add option "wrapTryCatch" to choose whether adding an outermost 
 * 							try{...}catch (Exception e){throw e} around each method to ensure no ReturnInto 
 * 							event would be missing 
 * 07/05/13		hcai		factor reusable code out as common utilities for the whole mcia project
 * 08/27/13		hcai		add option "statUncaught" to stat how often uncaught exception happens in runtime 
 *
*/
package EAS;

import java.util.ArrayList;
import java.util.List;

public class EAOptions {
	protected boolean debugOut = false;
	protected boolean dumpJimple = false;
	protected boolean sclinit = false;
	protected boolean wrapTryCatch = false;
	protected boolean dumpFunctionList = false;
	protected boolean statUncaught = false;

	public boolean debugOut() { return debugOut; }
	public boolean dumpJimple() { return dumpJimple; }
	public boolean sclinit() { return sclinit; }
	public boolean wrapTryCatch() { return wrapTryCatch; }
	public boolean dumpFunctionList() { return dumpFunctionList; }
	public boolean statUncaught() { return statUncaught; }
	public final static int OPTION_NUM = 6;
	
	public String[] process(String[] args) {
		List<String> argsFiltered = new ArrayList<String>();
		boolean allowPhantom = true;
		
		for (int i = 0; i < args.length; ++i) {
			String arg = args[i];

			if (arg.equals("-debug")) {
				debugOut = true;
			}
			else if (arg.equals("-dumpJimple")) {
				dumpJimple = true;
			}
			else if (arg.equals("-sclinit")) {
				sclinit = true;
			}
			else if (arg.equals("-wrapTryCatch")) {
				wrapTryCatch = true;
			}
			else if (arg.equals("-statUncaught")) {
				statUncaught = true;
			}
			else if (arg.equals("-dumpFunctionList")) {
				dumpFunctionList = true;
			}
			else if (arg.equals("-nophantom")) {
				allowPhantom = false;
			}
			else {
				argsFiltered.add(arg);
			}
		}
		
		if (allowPhantom) {
			argsFiltered.add("-allowphantom");
		}
		
		String[] arrArgsFilt = new String[argsFiltered.size()];
		return (String[]) argsFiltered.toArray(arrArgsFilt);
	}
}

/* vim :set ts=4 tw=4 tws=4 */

