/**
 * File: src/Diver/SVTNode.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created; model a VTG node on the static value transfer graph
 *  
*/
package Diver;

import java.util.Comparator;

import dua.method.CFGDefUses.Variable;
import fault.StmtMapper;

import soot.*;
import soot.jimple.*;

import MciaUtil.*;
import MciaUtil.CompleteUnitGraphEx.AugmentedUnit;

/** A static VTG node describes basic info about a variable w.r.t its service for value flow 
 * tracing of the variable 
 */
public class SVTNode implements IVTNode<Variable, SootMethod, Stmt>, Comparable<SVTNode> {
	/** variable underneath */
	protected final Variable v;
	/** enclosing/hosting method of the variable */
	protected final SootMethod m;
	/** statement location of the node */
	protected Stmt s;
	
	/** we may ignore stmt. loc. for some variables temporarily */
	public SVTNode(Variable _v, SootMethod _m) {
		v = _v;
		m = _m;
		s = null;
	}
	public SVTNode(Variable _v, SootMethod _m, Stmt _s) {
		v = _v;
		m = _m;
		s = _s;
	}
	
	/** accessors */
	void setStmt(Stmt _s) { this.s = _s; }
	public Variable getVar() { return v; }
	public SootMethod getMethod() { return m; }
	public Stmt getStmt() { return s; }

	@Override public int hashCode() {
		// NOTE: different types of variable can be assigned different hash code even though the underlying value is the same
		//return (m.hashCode() & 0xffff0000) | (v.hashCode() & 0x0000ffff);
		//return (m.hashCode() & 0xffff0000) | (v.getValue().hashCode() & 0x0000ffff);
		/*
		if (v.isLibCallObj() || v.isObject()) {
			return m.hashCode() + s.hashCode() + Util.objValueHashCode(v.getValue());
		}
		if ((v.isFieldRef() && ((FieldRef)v.getValue()).getField().isFinal())) {
			if (!((FieldRef)v.getValue()).getField().getDeclaringClass().isApplicationClass()) {
				if (s==null) {
					// library objects (System.out, say) do not have definition statement associated with 
					return m.hashCode() + v.getValue().hashCode();
				}
			}
		}
		
		if (v.isConstant() || v.isStrConstObj()) {
			return m.hashCode() + s.hashCode() + v.getValue().hashCode();
		}
		return m.hashCode() + Util.valueHashCode(v.getValue()) + s.hashCode();
		//return m.hashCode() + v.hashCode() + s.hashCode();
		*/
		
		//return m.hashCode() + s.hashCode() + v.getValue().hashCode();
		//return m.getSignature().hashCode() + v.getValue().toString().hashCode() + s.toString().hashCode();
		//return m.getSignature().hashCode() + v.getValue().hashCode() + s.toString().hashCode();
		return m.hashCode() + s.hashCode() + utils.getCanonicalFieldName(v).hashCode();
	}

	/** we do not distinguish two VTG nodes by statement location only */
	@Override public boolean equals(Object o) {
		//return v.mayEqualAndAlias(((SVTNode)o).v) && m == ((SVTNode)o).m;
		//return v == ((SVTNode)o).v && m == ((SVTNode)o).m;
		//return dua.util.Util.valuesEqual(v.getValue(), ((SVTNode)o).v.getValue(), true) && m == ((SVTNode)o).m;
		
		//return v.equals( ((SVTNode)o).v ) && m.equals( ((SVTNode)o).m );
		try {
			//return v.mayEqualAndAlias(((SVTNode)o).v) && m.equals( ((SVTNode)o).m );
			/*
			boolean b1 = v.mayEqualAndAlias(((SVTNode)o).v);
			if (v.isConstant() || v.isStrConstObj()) {
				b1 = v.getValue().equals(((SVTNode)o).v.getValue());
			}
			b1 = b1 && m.equals( ((SVTNode)o).m ) && s.equals( ((SVTNode)o).s );
			
			if (b1) return b1;
			
			if (b1 && (this.hashCode() != ((SVTNode)o).hashCode() )) {
				System.out.println("Yes Dear, Hash code conflicts: " + this + " and " + (SVTNode)o);
				System.exit(-1);
			}
			if (!b1) {
				boolean b2 = //m.getSignature().equalsIgnoreCase( ((SVTNode)o).m.getSignature()) && 
				StmtMapper.getGlobalStmtId(s)==4070;
				if (b2) {
					System.out.println("Yes Dear, got one: " + this + " and " + (SVTNode)o);
					if (!utils.getFlexibleStmtId(s).equals(utils.getFlexibleStmtId(((SVTNode)o).s))) {
						System.out.println("Wooo, their flexible stmt ids are not equal...");
						System.exit(-1);
					}
					if ( ! v.mayEqualAndAlias(((SVTNode)o).v) ) {
						System.out.println("Wooo, their variable values are not equalOrAlias, one is: "+ utils.getCanonicalFieldName(v) +
								" while another is: " + utils.getCanonicalFieldName (((SVTNode)o).v));
						System.exit(-1);
					}
					if (!s.equals( ((SVTNode)o).s)) {
						System.out.println("Wooo, their stmts  are not equal, one is: "+ s +
								" while another is: " + ((SVTNode)o).s);
						System.exit(-1);
					}
					if (!utils.getCanonicalFieldName(v).equalsIgnoreCase(utils.getCanonicalFieldName (((SVTNode)o).v))) {
						System.out.println("Wooo, their variable value is not equal, one is : " + utils.getCanonicalFieldName(v) +
								" while another is: " + utils.getCanonicalFieldName (((SVTNode)o).v));
						System.exit(-1);
					}
				}
			}
			*/
			/*
			if (v.isConstant() || v.isStrConstObj()) {
				return v.getValue().equals(((SVTNode)o).v.getValue()) && m.equals( ((SVTNode)o).m ) && s.equals( ((SVTNode)o).s );
			}
			return v.mayEqualAndAlias(((SVTNode)o).v) && m.equals( ((SVTNode)o).m ) && s.equals( ((SVTNode)o).s );
			*/
			return m.equals( ((SVTNode)o).m ) && s.equals( ((SVTNode)o).s ) && 
						( utils.getCanonicalFieldName(v).equalsIgnoreCase(utils.getCanonicalFieldName (((SVTNode)o).v)) ||
								v.mayEqualAndAlias(((SVTNode)o).v) );
			
		}
		catch (Exception e) {
			/** this is for the makeshift during Serialization of the "SootMethod" field of SVTNode ONLY */
			/*
			return utils.getCanonicalFieldName(v).equalsIgnoreCase(utils.getCanonicalFieldName (((SVTNode)o).v)) &&
						m.getName().equalsIgnoreCase( ((SVTNode)o).m.getName());
			*/
			/*
			return utils.getCanonicalFieldName(v).equalsIgnoreCase(utils.getCanonicalFieldName (((SVTNode)o).v)) &&
						m.getName().equalsIgnoreCase( ((SVTNode)o).m.getName()) &&
						s.toString().equalsIgnoreCase( ((SVTNode)o).s.toString());
			*/
			return m.getSignature().equalsIgnoreCase( ((SVTNode)o).m.getSignature()) &&
						s.toString().equalsIgnoreCase( ((SVTNode)o).s.toString()) && 
						utils.getCanonicalFieldName(v).equalsIgnoreCase(utils.getCanonicalFieldName (((SVTNode)o).v));
					//utils.getFlexibleStmtId(s).equals(utils.getFlexibleStmtId(((SVTNode)o).s));
		}
	}
	/* exactly equal comparator */
	public boolean strictEquals(Object o) {
		//return this == o && s == ((SVTNode)o).s;
		return this.equals(o) && s.equals( ((SVTNode)o).s );
	}
	public String toStringNoStmt() {
		//return "("+utils.getCanonicalFieldName(v)+","+m.getName()+")";
		return "("+utils.getCanonicalFieldName(v)+","+m.getSignature()+")";
	}
	@Override public String toString() {
		if (null != s) {
			String sid = "";
			try {
				sid += StmtMapper.getGlobalStmtId(s);
			}
			catch(Exception e) {
				if (s instanceof ReturnStmt && ((ReturnStmt)s).getOp() instanceof IntConstant) {
					/** this is for the makeshift during Serialization of the "Stmt" field of SVTNode ONLY */
					sid += ( (IntConstant) ((ReturnStmt)s).getOp() ).toString();
				}
				else {
					sid = "unknown";
				}
			}
			//return "("+utils.getCanonicalFieldName(v)+","+m.getDeclaringClass().getName()+"::"+m.getName()+","+sid+")";
			return "("+utils.getCanonicalFieldName(v)+","+m.getSignature()+","+sid+")";
		}
		//return "("+utils.getCanonicalFieldName(v)+","+m.getDeclaringClass().getName()+"::"+m.getName()+")";
		return "("+utils.getCanonicalFieldName(v)+","+m.getSignature()+")";
	}
	
	public int compareTo(SVTNode other) {
		return SVTNodeComparator.inst.compare(this, other);
	}

	public static class SVTNodeComparator implements Comparator<SVTNode> {
		private SVTNodeComparator() {}
		public static final SVTNodeComparator inst = new SVTNodeComparator();

		public int compare(SVTNode n1, SVTNode n2) {
			final String mname1 = n1.m.getSignature();
			final String mname2 = n2.m.getSignature();

			final String vname1 = n1.v.isConstant()? ((Constant)n1.v.getValue()).toString() : n1.v.toString();
			final String vname2 = n2.v.isConstant()? ((Constant)n2.v.getValue()).toString() : n2.v.toString();

			int cmpmName = mname1.compareToIgnoreCase(mname2);
			int cmpvName = vname1.compareToIgnoreCase(vname2);
			if (null == n1.s || null == n2.s || 
					n1.s instanceof AugmentedUnit ||
					n2.s instanceof AugmentedUnit) {
				return (cmpmName != 0)?cmpmName : cmpvName; 
			}

			final int sid1 = StmtMapper.getGlobalStmtId(n1.s);
			final int sid2 = StmtMapper.getGlobalStmtId(n2.s);
			return (cmpmName != 0)?cmpmName : (cmpvName != 0)?cmpvName:
				(sid1 > sid2)?1:(sid1 < sid2)?-1:0;
		}
	}
}

/* vim :set ts=4 tw=4 tws=4 */
