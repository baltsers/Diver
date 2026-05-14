/**
 * File: src/McaiUtil/MHGPostDominatorsFinderEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/10/13		hcai		created; extending MHGDominatorsFinder for fixing Soot 2.3.0 bugs in this class
 *  
*/
package MciaUtil;

import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
	
/**
 * An extension of  MHGDominatorsFinder to adapt to the cases in which there are nodes that do not
 * have any "strict dominator", which happens when this is used for actually a PDT which has multiple
 * heads;
 * 
 * More importantly, this extension is made in order to fix the bug found at the following line
 * fullSet.flip(0, graph.size());//set all to true
 * originally it was 
 * fullSet.flip(0, graph.size()-1);//set all to true
 * Note: this bug has been fixed in the latest release of Soot (2.5.0). For Soot 2.3.0 we are using
 * now, though, we still need this extension
 */
public class MHGDominatorsFinderEx extends MHGDominatorsFinder {
	public MHGDominatorsFinderEx(DirectedGraph g) { super(g); }
	@Override 
	public Object getImmediateDominator(Object node) {
		// root node
        if(getGraph().getHeads().contains(node))
            return null;

        List dominatorsList = getDominators(node);
        dominatorsList.remove(node);

        Iterator dominatorsIt = dominatorsList.iterator();
        Object immediateDominator = null;

        while((immediateDominator == null) && dominatorsIt.hasNext()){
            Object dominator = dominatorsIt.next();

            if(isDominatedByAll(dominator, dominatorsList))
                immediateDominator = dominator;
        }
        if (immediateDominator==null) {
        	System.out.println("[Warning]: a non-head node [" + node + "] does not have dominator! ");
        }
        //assert immediateDominator!=null;
        
        return immediateDominator;
	}
	@Override
	protected void doAnalysis()
    {
        heads = graph.getHeads();
        nodeToFlowSet = new HashMap<Object, BitSet>();
        nodeToIndex = new HashMap<Object, Integer>();
        indexToNode = new HashMap<Integer, Object>();
    
        //build full set
        fullSet = new BitSet(graph.size());
        fullSet.flip(0, graph.size());//set all to true
        
        //set up domain for intersection: head nodes are only dominated by themselves,
        //other nodes are dominated by everything else
        for(Iterator i = graph.iterator(); i.hasNext();){
            Object o = i.next();
            if(heads.contains(o)){
                BitSet self = new BitSet();
                self.set(indexOf(o));
                nodeToFlowSet.put(o, self);
            }
            else{
                nodeToFlowSet.put(o, fullSet);
            }
        }

        boolean changed = true;
        do{
            changed = false;
            for(Iterator i = graph.iterator(); i.hasNext();){
                Object o = i.next();
    
                //set up domain for intersection: head nodes are only dominated by themselves,
                //other nodes are dominated by everything else
                BitSet predsIntersect;
                if(heads.contains(o)) {
                    predsIntersect = new BitSet();
                    predsIntersect.set(indexOf(o));
                }
                else
                    //this clone() is fast on BitSets (opposed to on HashSets)
                    predsIntersect = (BitSet) fullSet.clone();
    
                //intersect over all predecessors
                for(Iterator j = graph.getPredsOf(o).iterator(); j.hasNext();){
                    BitSet predSet = (BitSet) nodeToFlowSet.get(j.next());
                    predsIntersect.and(predSet);
                }
    
                BitSet oldSet = (BitSet)nodeToFlowSet.get(o);
                //each node dominates itself
                predsIntersect.set(indexOf(o));
                if(!predsIntersect.equals(oldSet)){
                    nodeToFlowSet.put(o, predsIntersect);
                    changed = true;
                }
            }
        } while(changed);
    }
}

/* vim :set ts=4 tw=4 tws=4 */
