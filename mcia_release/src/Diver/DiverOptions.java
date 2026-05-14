/**
 * File: src/Diver/DiverOptions.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/05/13		hcai		created; for command-line argument processing for EAS Instrumenter
 * 07/05/13		hcai		factor reusable code out as common utilities for the whole mcia project 
 * 08/15/13		hcai		added options for computing and incorporating intra- and inter- procedural CDs
 * 08/17/13		hcai		added options for visualizing VTG (applicable to both static and dynamic ones)
 * 08/21/13		hcai		added automatic VTG validation option
 * 09/01/13		hcai		added options for creating interprocedural exceptional CDs due to uncaught exceptions
 *
*/
package Diver;

import java.util.ArrayList;
import java.util.List;
import EAS.*;

public class DiverOptions extends EAOptions {
	/* if serializing the static VTG at the end of the static analysis phase */
	protected boolean serializeVTG = false;
	/* if considering Intraprocedural CDs */
	protected boolean intraCD = false;
	/* if considering Interprocedural CDs */
	protected boolean interCD = false;
	/* if visualize the eventual VTG, namely the MDG (method dependence graph) */
	protected boolean visualizeVTG = false;
	/* safety check against the static VTG */
	protected boolean validateVTG = false;
	/* if adding exceptional interprocedural CDs due to uncaught exceptions */
	protected boolean exceptionalInterCD = false;
	/* if ignoring RunimeException exceptions when considering the exceptional interprocedural CDs due to uncaught exceptions */
	protected boolean ignoreRTECD = false;
	
	/* for dynamic alias monitoring expressly: cache until the end of execution or dump immediately */
	protected boolean cachingOIDs = false;

	public final static int OPTION_NUM = EAOptions.OPTION_NUM + 8;
	
	@Override public String[] process(String[] args) {
		args = super.process(args);
		
		List<String> argsFiltered = new ArrayList<String>();
		for (int i = 0; i < args.length; ++i) {
			String arg = args[i];

			if (arg.equals("-serializeVTG")) {
				serializeVTG = true;
			}
			else if (arg.equals("-intraCD")) {
				intraCD = true;
			}
			else if (arg.equals("-interCD")) {
				interCD = true;
			}
			else if (arg.equals("-visualizeVTG")) {
				visualizeVTG = true;
			}
			else if (arg.equals("-validateVTG")) {
				validateVTG = true;
			}
			else if (arg.equals("-exInterCD")) {
				exceptionalInterCD = true;
			}
			else if (arg.equals("-ignoreRTECD")) {
				ignoreRTECD = true;
			}
			else if (arg.equals("-cachingOIDs")) {
				cachingOIDs = true;
			}
			else {
				argsFiltered.add(arg);
			}
		}
		
		String[] arrArgsFilt = new String[argsFiltered.size()];
		return (String[]) argsFiltered.toArray(arrArgsFilt);
	}
}

/* vim :set ts=4 tw=4 tws=4 */

