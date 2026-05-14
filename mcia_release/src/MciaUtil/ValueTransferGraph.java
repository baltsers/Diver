/**
 * File: src/MciaUtil/ValueTransferGraph.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 07/05/13		hcai		created; a base model of value transfer graph used in the mcia project
 * 08/17/13		hcai		added VTG visualization using Graphviz DotGraph offered by Soot
 *  
*/
package MciaUtil;

import java.io.*;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import soot.util.dot.DotGraph;
import soot.util.dot.DotGraphAttribute;
import soot.util.dot.DotGraphConstants;
import soot.util.dot.DotGraphEdge;
import soot.util.dot.DotGraphNode;

import MciaUtil.VTEdge.VTEType;

/** the skeleton of value transfer graph (VTG) that models value flow relations between variables, 
 * both intra- and inter-procedurally, serving as the base class for both static and dynamic VTGs
 *
 * VTG serves tracing value flow of variables that potentially propagates the impacts of original changes
 * 
 * <i>VTNodeT</i> is the type of the graph nodes, and <i>VTEdgeT</i> the graph edges
 */
abstract public class ValueTransferGraph <VTNodeT, VTEdgeT extends VTEdge<VTNodeT>> implements Serializable {
	/** data members of a Value Transfer Graph */
	/** all nodes */
	transient protected Set<VTNodeT> nodes; 
	/** all edges */
	transient protected Set<VTEdgeT> edges;
	/** map from a node to all outgoing edges */
	transient protected Map< VTNodeT, Set<VTEdgeT> > nodeToEdges;
	
	protected void initInternals() {
		nodes = new LinkedHashSet<VTNodeT>();
		edges = new LinkedHashSet<VTEdgeT>();
		nodeToEdges = new LinkedHashMap< VTNodeT, Set<VTEdgeT> >();
	}
	public ValueTransferGraph() {
		initInternals();
	}
	
	public boolean isEmpty() {
		return nodes.isEmpty() || edges.isEmpty() || nodeToEdges.isEmpty();
	}
	public void clear() {
		nodes.clear();
		edges.clear();
		nodeToEdges.clear();
	}
	
	@Override public String toString() {
		return "Value Transfer Graph: " + nodes.size() + " nodes, " + edges.size() + " edges ";
	}
	
	public void CopyFrom(ValueTransferGraph<VTNodeT, VTEdgeT> vtg) {
		this.clear();
		
		this.nodes = vtg.nodes;
		this.edges = vtg.edges;
		this.nodeToEdges = vtg.nodeToEdges;
	}
	
	/** accessors */
	public Set<VTNodeT> nodeSet() { return nodes; }
	public Set<VTEdgeT> edgeSet() { return edges; }
	public Set<VTEdgeT> getOutEdges(VTNodeT _node) { return nodeToEdges.get(_node); }

	// descendants must create the edge
	abstract protected void createTransferEdge(VTNodeT src, VTNodeT tgt, VTEType etype);

	// descendants must create the graph itself	
	abstract public int buildGraph(boolean debugOut) throws Exception;
	
	abstract public void addEdge(VTEdgeT edge);
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    private static final long serialVersionUID = 0x438200DE;
  
	/**
	 * Serialize the static VTG to a disk file whose name is given by sfn
	 * @param sfn the name of disk file into which the static VTG is to be dumped
	 * @return 0 for success and others for failure
	 */
	public int SerializeToFile(String sfn) {
		if ( !sfn.isEmpty() ) {
			FileOutputStream fos;
			try {
				fos = new FileOutputStream(sfn);
				ObjectOutputStream oos = new ObjectOutputStream(fos);
				oos.writeObject(this);
				//this.writeObject(oos);
				oos.flush();
				oos.close();
				return 0;
			}
			catch (Exception e) {
				e.printStackTrace();
				return -1;
			}
		}
		return -2;
	} // SerializeToFile
	
	public Object DeserializeFromFile(String dfn) {
		FileInputStream fis;
		try {
			fis = new FileInputStream(dfn);
			
			// reconstruct the static VTG from the given disk file 
			ObjectInputStream ois = new ObjectInputStream(fis);
			return ois.readObject();
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the source file from which the VTG is deserialized specified as " + dfn);
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to ValueTransferGraph!");
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	} // DeserializeFromFile
	
	/**
	 * for debugging purposes, list all edge details
	 * @param listByEdgeType
	 * @return 0 - already done; 1 - more needed
	 */
	public int dumpGraphInternals(boolean listByEdgeType) {
		System.out.println(this);
		
		if (!listByEdgeType) {
			/* list all edges */
			for (VTEdgeT edge : edges) {
				System.out.println(edge);
			}
			return 0;
		}
		
		return 1;
		
		// descendants need do more
		// -
	} // dumpGraphInternals
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           VISUALIZATION OF VTG (w.r.t DotGraph@Graphviz)
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	/** Serialize the VTG into DotGraph format, which can be rendered by Graphviz Dot */
	public int visualizeVTG(String filename) {
		if (filename.length() < 1) {
			// invalid name
			return -1;
		}
		
		String graphname = "Method Dependence Graph";
		final DotGraph canvas = new DotGraph(graphname);
		final DotGraphAttribute defaultNodeColor = new DotGraphAttribute("color", "black");
		final DotGraphAttribute defaultEdgeColor = new DotGraphAttribute("color", "black");
		
		// basic DotGraph settings
		canvas.setPageSize(8.5, 11.0);
		canvas.setNodeShape(DotGraphConstants.NODE_SHAPE_BOX);
		canvas.setNodeStyle(DotGraphConstants.NODE_STYLE_SOLID);
		canvas.setGraphLabel(graphname);
		canvas.setOrientation(DotGraphConstants.GRAPH_ORIENT_LANDSCAPE);
		
		// draw all nodes and edges
		for (VTNodeT node : nodes) {
			Set<VTEdgeT> allOutEdges = getOutEdges(node);
			if (null == allOutEdges) {
				// no successors, done
				continue;
			}
			for (VTEdgeT edge : allOutEdges) {
				DotGraphNode dotNode = canvas.drawNode(node.toString());
				dotNode.setAttribute(defaultNodeColor);
				dotNode.setLabel(node.toString());
				
				DotGraphEdge dotEdge = canvas.drawEdge(node.toString(), edge.getTarget().toString());
				dotEdge.setAttribute(defaultEdgeColor);
				dotEdge.setLabel(VTEdge.edgeTypeLiteral(edge.getEdgeType()));
				
				// Optional: discern edge types by color
				if (edge.isControlEdge()) {
					dotEdge.setAttribute("color", "red");
				}
				if (edge.isAdjacentEdge()) {
					dotEdge.setAttribute("color", "blue");
				}
				if (edge.isHeapEdge()) {
					dotEdge.setAttribute("color", "lightgray");
				}
				
				if (edge.isLocalEdge()) {
					dotEdge.setStyle(DotGraphConstants.EDGE_STYLE_SOLID);
				}
				else if (!edge.isControlEdge()){
					dotEdge.setStyle(DotGraphConstants.EDGE_STYLE_DOTTED);
				}
				
			} // for each outgoing edge starting from the current Node
		} // for each graph Node
		
		canvas.plot(filename);
		return 0;
	}
} // definition of ValueTransferGraph

/* vim :set ts=4 tw=4 tws=4 */
