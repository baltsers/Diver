/**
 * File: src/MciaUtil/VTEdge.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created; a base class for an edge on the Value Transfer Graph
 *  
*/
package MciaUtil;

import java.util.Comparator;
import java.util.Map;

/** An edge as a component of VTG models the value flow relation from a writer (source)
 * to a reader (target) of a variable
 */
public class VTEdge<VTNodeT> implements IVTEdge<VTNodeT> {
	/** possible value transfer edge types */
	public static enum VTEType { VTE_UNKNOWN, VTE_STVAR, VTE_INSVAR, 
		VTE_PARAM, VTE_RET, VTE_PARARET, VTE_INTRA, VTE_ALIAS, VTE_ARRAYELE, VTE_LIBOBJ,
		VTE_CONTROL_INTRA, VTE_CONTROL_INTER};
		
	public static	final String[] typeLiterals = new String[] {
		"unknown", "staticVariableEdge", "instanceVariableEdge", "parameterEdge",
			"returnEdge", "refParamReturnEdge", "intraproceduralEdge", "aliasEdge", "arrayEleEdge", "libObjEdge",
			"IntraControlEdge", "InterControlEdge"};

	public static String edgeTypeLiteral(VTEType _etype) {
		return typeLiterals[_etype.ordinal() - VTEType.VTE_UNKNOWN.ordinal()];
	}
	// edges active only within in a method
	public static boolean isLocalType(VTEType etype) { 
		return etype==VTEType.VTE_INTRA || etype==VTEType.VTE_ALIAS; }
	// edges active between two adjacent methods
	public static boolean isAdjacentType(VTEType etype) { 
		return etype==VTEType.VTE_PARAM || etype==VTEType.VTE_RET || etype==VTEType.VTE_PARARET;} 
	// edges active across any two methods
	public static boolean isHeapType(VTEType etype) { 
		return etype==VTEType.VTE_INSVAR || etype==VTEType.VTE_STVAR || 
					etype==VTEType.VTE_ARRAYELE || etype==VTEType.VTE_LIBOBJ;} 
	// control dependencies
	public static boolean isControlType(VTEType etype) {
		return etype ==VTEType.VTE_CONTROL_INTRA || etype ==VTEType.VTE_CONTROL_INTER; }
	
	/** A VTG node describes basic info about a variable w.r.t its service for value flow 
	 * tracing of the variable 
	 */
	/* since dynamic and static VTG have very different VTG node types in terms of their internal data structure, and also it
	 * is hard to build a template for both, we abstract the VTG node type out as the incoming template parameter
	 */
	protected final VTNodeT src;
	protected final VTNodeT tgt;
	protected final VTEType etype;

	/** accessors */
	public VTNodeT getSource() { return src; }
	public VTNodeT getTarget() { return tgt; }
	public VTEType getEdgeType() { return etype; }
	/** determinants */
	public boolean isParameterEdge() { return VTEType.VTE_PARAM == etype; }
	public boolean isStaticVarEdge() { return VTEType.VTE_STVAR == etype; }
	public boolean isInstanceVarEdge() { return VTEType.VTE_INSVAR == etype; }
	public boolean isReturnEdge() { return VTEType.VTE_RET == etype; }
	public boolean isRefReturnParamEdge() { return VTEType.VTE_PARARET == etype; }
	public boolean isIntraEdge() { return VTEType.VTE_INTRA == etype; }
	public boolean isAliasEdge() { return VTEType.VTE_ALIAS == etype; }
	public boolean isArrayEleEdge() { return VTEType.VTE_ARRAYELE == etype; }
	public boolean isLibObjEdge() { return VTEType.VTE_LIBOBJ == etype; }
	public boolean isIntraControlEdge() { return VTEType.VTE_CONTROL_INTRA == etype; }
	public boolean isInterControlEdge() { return VTEType.VTE_CONTROL_INTER == etype; }
	
	/* coarser classification of edges */
	// edges active only within in a method
	public boolean isLocalEdge() { return isIntraEdge() || isAliasEdge(); }
	// edges active between two adjacent methods
	public boolean isAdjacentEdge() { return isParameterEdge() || isReturnEdge() || isRefReturnParamEdge(); }
	// edges active across any two methods
	public boolean isHeapEdge() { return isStaticVarEdge() || isInstanceVarEdge() || isArrayEleEdge() || isLibObjEdge(); }
	// edges active within a method or across two methods
	public boolean isControlEdge() { return isIntraControlEdge() || isInterControlEdge(); }
	
	public VTEdge(VTNodeT _src, VTNodeT _tgt, VTEType _etype) { 
		src = _src; 
		tgt = _tgt;
		etype = _etype;
	}

	@Override public int hashCode() {
		//return (src.hashCode() & 0xffff0000) | (tgt.hashCode() & 0x0000ffff);  
		return src.hashCode() + tgt.hashCode() + etype.ordinal();
	}
	/** we do not distinguish two VTG nodes by statement location only */
	@SuppressWarnings("unchecked")
	@Override public boolean equals(Object o) {
		return src.equals(((VTEdge<VTNodeT>)o).src) && tgt.equals( ((VTEdge<VTNodeT>)o).tgt ) 
				&& etype == ((VTEdge<VTNodeT>)o).etype;
	}
	/** exactly equal comparator */
	@SuppressWarnings("unchecked")
	public boolean strictEquals(Object o) {
		return src == (((VTEdge<VTNodeT>)o).src) && tgt == (((VTEdge<VTNodeT>)o).tgt) 
			&& etype == ((VTEdge<VTNodeT>)o).etype;
	}
	public String toString(boolean withType) {
		String ret = "<";
		ret += src;
		ret += ",";
		ret += tgt;
		ret += ">";
		if (withType) {
			ret += ":" + edgeTypeLiteral(etype);
		}
		return ret;
	}
	@Override public String toString() {
		return toString(true);
	}

	public static class VTEdgeComparator implements Comparator<VTEdge<?>> {
		private final Map<VTEdge<?>, Integer> edgeIds;
		public VTEdgeComparator(Map<VTEdge<?>, Integer> _edgeIds) { edgeIds = _edgeIds; }

		public int compare(VTEdge<?> e1, VTEdge<?> e2) {
			final int eid1 = edgeIds.get(e1);
			final int eid2 = edgeIds.get(e2);

			return (eid1 > eid2)?1:(eid1 < eid2)?-1:0;
		}
	}

} // definition of VTEdge

/* vim :set ts=4 tw=4 tws=4 */
