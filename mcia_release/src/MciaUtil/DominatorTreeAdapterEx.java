/**
 * File: src/McaiUtil/DominatorTreeAdapterEx.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/10/13		hcai		created; extending DominatorTreeAdapter for accommodating DominatorTreeEx
 *  
*/
package MciaUtil;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.DominatorNode;

/**
 * An adaptation of DominatorTreeAdapter in order to accommodate the cases in which the 
 * underlying CFG is a multi-headed DominatorsFinder  
 */
public class DominatorTreeAdapterEx implements DirectedGraph
{
    DominatorTreeEx dt;
    
    public DominatorTreeAdapterEx(DominatorTreeEx dt)
    {
        this.dt = dt;
    }

    public List getHeads()
    {
        return dt.getHeads();
    }

    public List getTails()
    {
        return dt.getTails();
    }
    /*
    public List getPredsOf(Object node)
    {
        return dt.getPredsOf((DominatorNode)node); 
    }

    public List getSuccsOf(Object node)
    {
        return dt.getSuccsOf((DominatorNode)node);
    }
    */
    public List getPredsOf(Object node)
    {
        return Collections.singletonList(dt.getParentOf((DominatorNode)node));
    }

    public List getSuccsOf(Object node)
    {
        return dt.getChildrenOf((DominatorNode)node);
    }

    public Iterator iterator()
    {
        return dt.iterator();
    }

    public int size()
    {
        return dt.size();
    }
}

/* vim :set ts=4 tw=4 tws=4 */
