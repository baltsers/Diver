/**
 * File: src/MciaUtil/IVTNode.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created, defining interfaces for a VTG node
 * 
*/
package MciaUtil;

public interface IVTNode <VT, MT, ST> {
	public VT getVar();
	public MT getMethod();
	public ST getStmt();
	
	public int hashCode();
	public boolean equals(Object o);
	public String toString();
}

/* vim :set ts=4 tw=4 tws=4 */

