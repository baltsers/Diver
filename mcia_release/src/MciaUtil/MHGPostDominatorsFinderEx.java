/**
 * File: src/McaiUtil/MHGPostDominatorsFinderEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/10/13		hcai		created; extending MHGPostDominatorsFinder for applying MHGDominatorsFinderEx
 *  
*/
package MciaUtil;

import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.InverseGraph;
	
/**
 *  An extension of  MHGPostDominatorsFinder to adapt to the cases in which there are nodes that do not
 * have any "strict dominator", which happens when this is used for actually a PDT which has multiple
 * heads; A PostDominatorFinder is simply a DominatorsFinder that inputs an inverse CFG
 */
public class MHGPostDominatorsFinderEx extends MHGDominatorsFinderEx
{
	public MHGPostDominatorsFinderEx(DirectedGraph graph) {
		super(new InverseGraph(graph));
	}
}

/* vim :set ts=4 tw=4 tws=4 */
