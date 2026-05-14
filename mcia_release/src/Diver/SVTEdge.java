/**
 * File: src/Diver/SVTEdge.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created; model a VTG edge on the static value transfer graph
 *  
*/
package Diver;

import MciaUtil.*;

/** A static VTG edge as a component of VTG models the value flow relation from a writer (source)
 * to a reader (target) of a variable
 */
public class SVTEdge extends VTEdge<SVTNode> {
	public SVTEdge(SVTNode _src, SVTNode _tgt, VTEType _etype) {
		super(_src, _tgt, _etype);
	}
	/** exactly equal comparator */
	public boolean strictEquals(Object o) {
		return src.strictEquals(((SVTEdge)o).src) && tgt.strictEquals(((SVTEdge)o).tgt) 
			&& etype == ((SVTEdge)o).etype;
	}
	public String toString(boolean withStmt, boolean withType) {
		String ret = "<";
		ret += (withStmt)?src : src.toStringNoStmt();
		ret += ",";
		ret += (withStmt)?tgt : tgt.toStringNoStmt();
		ret += ">";
		if (withType) {
			ret += ":" + VTEdge.edgeTypeLiteral(etype);
		}
		return ret;
	}
	@Override public String toString() {
		return toString(true, true);
	}
	
	public boolean isInterproceduralEdge() { return src.getMethod() != tgt.getMethod(); }
}

/* vim :set ts=4 tw=4 tws=4 */
