/**
 * File: src/MciaUtil/IVTEdge.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created, defining interfaces for a VTG edge
 * 
*/
package MciaUtil;

public interface IVTEdge <NT> {
	public NT getSource();
	public NT getTarget();
	
	public int hashCode();
	public boolean equals(Object o);
	public String toString();
}

/* vim :set ts=4 tw=4 tws=4 */

