/**
 * File: src/McaiUtil/DominatorTreeEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/10/13		hcai		created; extending DominatorTree for accommodating multi-heads
 *  
*/
package MciaUtil;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import soot.toolkits.graph.DominatorNode;
import soot.toolkits.graph.DominatorTree;
import soot.toolkits.graph.DominatorsFinder;
	
/**
 * An extension of DominatorTree in order to accommodate the cases in which the 
 * underlying CFG is a multi-headed DominatorsFinder  
 */
//@SuppressWarnings("unchecked")
public class DominatorTreeEx extends DominatorTree {
	protected ArrayList<DominatorNode> heads;
	public DominatorTreeEx(DominatorsFinder dominators) { super(dominators);}

	public List<DominatorNode> getHeads() {
        return (List<DominatorNode>) heads.clone();
    }

    /** This overrides the parent buildTree to allow multiple heads.
     *   Mostly copied from the super class and modified.
     */
	@Override
    protected void buildTree()
    {
    	// hook up children with parents and vice-versa
    	this.heads = null;
        for(Iterator godesIt = graph.iterator(); godesIt.hasNext();) {
            Object gode = godesIt.next();

            DominatorNode dode = fetchDode(gode);
            DominatorNode parent = fetchParent(gode);

            if(parent == null){
	             //make sure the array is created!
	             if(heads == null)
	                 heads = new ArrayList();

	             heads.add(dode);
            }
            else{
                parent.addChild(dode);
                dode.setParent(parent);
            }
        }
      
        //head = (DominatorNode) heads.get(0);
       
        // identify the tail nodes
        
        for(Iterator dodesIt = this.iterator(); dodesIt.hasNext();) {
            DominatorNode dode = (DominatorNode) dodesIt.next();
            if(dode.isTail())
                tails.add(dode);
        }
        
        ////////////////////////////////////////////////////////////////////////////////////////////////////////
        /** after the "real" dominator tree" is built, we add the START/STOP nodes to facilitate 
         * CDG construction following immediately
         */
        /*
        // 1. add a START node connecting to each of all the heads (so far, I have not seen any multi-head CFG)
        AugmentedUnit startUnit = new AugmentedUnit("START");
        
        // 2. add a STOP node joining all exits in the control flow graph
        AugmentedUnit stopUnit = new AugmentedUnit("STOP");
        */
    }
	
	 public DominatorNode getHead() {
		 return (DominatorNode) heads.get(0);
	 }
}


/* vim :set ts=4 tw=4 tws=4 */
