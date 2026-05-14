/**
 * File: src/MciaUtil/CDEdgeVar.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/14/13		hcai		created; model a concrete variable that can meet needs of representing
 *							the "Variable component" in the VTG node at a CD edge source or target,
 *							hold almost all types of Values, which any CD edge vertex could be of.
 *  
*/
package MciaUtil;

import java.util.BitSet;
import dua.global.p2.P2Analysis;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.StdVariable;
import dua.method.CFGDefUses.ObjVariable;
import dua.method.CFGDefUses.Variable;

import soot.*;
import soot.jimple.*;

/**
 * A versatile Variable, hosting not only conditionExpr though, used for modeling the "variable" component in
 * a SVTNode for intraCD edge vertices, esp. those having no defined variables, which we need to incorporate CDs into
 * value transfer graph
 */
public class CDEdgeVar extends Variable {
	protected final StdVariable svar;
	protected final ObjVariable ovar;
	protected final Value op1;
	protected final Value op2;
	protected final CFGNode n;
	
	public CDEdgeVar(Value val, CFGNode _n) { 
		super(val);
		n = _n;
		svar = new StdVariable(val);
		ovar = new ObjVariable(val,_n);
		if (isCondition()) {
			ConditionExpr ce = (ConditionExpr)val;
			op1 = ce.getOp1();
			op2 = ce.getOp2();
		}
		else {
			op1 = op2 = null;
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj.getClass() == CDEdgeVar.class)) return false;
		CDEdgeVar conObj = (CDEdgeVar)obj;
		if (isCondition()) {
			if ( !conObj.isCondition() ) return false;
			return dua.util.Util.valuesEqual(op1, conObj.op1, true) && dua.util.Util.valuesEqual(op2, conObj.op2, true);
		}
		if (isObject() || isStrConstObj() || isLibCallObj()) {
			return ovar.equals(conObj.ovar);
		}
		return svar.equals(conObj.svar);
	}
	
	@Override
	public int hashCode() {
		if (isCondition()) {
			return op1.hashCode() + op2.hashCode();
		}
		if (isObject() || isStrConstObj() || isLibCallObj()) {
			return ovar.hashCode();
		}
		return svar.hashCode();
	}
	
	@Override
	public String toString() {
		if (isCondition()) {
			return "CondVar: " + val.toString();
		}
		if (isObject() || isStrConstObj() || isLibCallObj()) {
			return "ObjCDSrc: " + ovar.toString();
		}
		return "StdCDSrc: " + svar.toString();
	}

	@Override public boolean isConstant() { return val instanceof Constant; }
	@Override public boolean isLocal() { return val instanceof Local; }
	@Override public boolean isLocalOrConst() { return isLocal() || isConstant(); }
	@Override public boolean isFieldRef() { return val instanceof FieldRef; }
	@Override public boolean isArrayRef() { return val instanceof ArrayRef; }
	@Override public boolean isObject() { return val instanceof AnyNewExpr || val instanceof ClassConstant; }
	@Override public boolean isStrConstObj() { return val instanceof StringConstant; }
	@Override public boolean isLibCallObj() { return val instanceof InvokeExpr; }
	@Override public boolean isReturnedVar() { return false; }
	@Override public boolean isDefinite() { return false; }
	
	public boolean isCondition() { return val instanceof ConditionExpr; }
	@Override
	public boolean mayEqual(Variable vOther) {
		if (!(vOther.getClass() == CDEdgeVar.class)) return false;
		CDEdgeVar conObj = (CDEdgeVar)vOther;
		if (isCondition()) {
			if ( !conObj.isCondition() ) return false;
			return dua.util.Util.valuesEqual(op1, conObj.op1, false) && dua.util.Util.valuesEqual(op2, conObj.op2, false);
		}
		if (isObject() || isStrConstObj() || isLibCallObj()) {
			return ovar.mayEqual(conObj.ovar);
		}
		return svar.mayEqual(conObj.svar);
	}

	@Override
	protected boolean mayAlias(Variable vOther) {
		if (isCondition() || !(vOther instanceof CDEdgeVar)) {
			return false;
		}
		
		if (isObject() || isStrConstObj() || isLibCallObj()) {
			CDEdgeVar objVar = (CDEdgeVar) vOther;
			
			// handle non-instance case
			if (val instanceof StaticInvokeExpr) {
				if (!(objVar.val instanceof StaticInvokeExpr))
					return false;
				SootClass clsThis = ((StaticInvokeExpr)this.val).getMethodRef().declaringClass(); // not the same as getMethod().getDeclaringClas() !!!
				SootClass clsOther = ((StaticInvokeExpr)objVar.val).getMethodRef().declaringClass(); // not the same as getMethod().getDeclaringClas() !!!
				return clsThis.equals(clsOther);
			}
			if (objVar.val instanceof StaticInvokeExpr)
				return false;
			
			// instances: compare p2 sets
			BitSet p2This = this.getP2Set();
			BitSet p2Other = objVar.getP2Set();
			// *** Handle DEGENERATE case in which P2 analysis does NOT provide info, but vars match ***
			if (p2This.isEmpty() && p2Other.isEmpty()) {
				// special case: both are str constants
				if (this.val instanceof StringConstant && objVar.val instanceof StringConstant)
					return this.n == objVar.n && this.val.equals(objVar.val);
				// special case: both are class constants (one class constant object per class => they must alias)
				if (this.val instanceof ClassConstant && objVar.val instanceof ClassConstant)
					return this.val.equals(objVar.val);
				// special case: both are static fld refs
				if (this.val instanceof StaticFieldRef && objVar.val instanceof StaticFieldRef)
					return this.val.equals(objVar.val);
				// if only one is a str const, that local will be null and the result will be false
				Local lBaseThis = getBaseLocal();
				Local lBaseOther = objVar.getBaseLocal();
				return lBaseThis == lBaseOther;
			}
			else
				return p2This.intersects(p2Other);
		}
		
		// compare p2 sets of bases, if they have bases
		if (val instanceof InstanceFieldRef) {
			Local lBaseThis = (Local) ((InstanceFieldRef)this.val).getBase();
			BitSet p2BaseThis = P2Analysis.inst().getP2Set(lBaseThis);
			Local lBaseOther = (Local) ((InstanceFieldRef)vOther.getValue()).getBase();
			BitSet p2BaseOther = P2Analysis.inst().getP2Set(lBaseOther);
			return p2BaseThis.intersects(p2BaseOther) ||
				   (p2BaseThis.isEmpty() && p2BaseOther.isEmpty() && lBaseThis == lBaseOther);
		}
		else if (val instanceof ArrayRef) {
			Local lBaseThis = (Local) ((ArrayRef)this.val).getBase();
			BitSet p2BaseThis = P2Analysis.inst().getP2Set(lBaseThis);
			Local lBaseOther = (Local) ((ArrayRef)vOther.getValue()).getBase();
			BitSet p2BaseOther = P2Analysis.inst().getP2Set(lBaseOther);
			return p2BaseThis.intersects(p2BaseOther) ||
				   (p2BaseThis.isEmpty() && p2BaseOther.isEmpty() && lBaseThis == lBaseOther);
		}
		return true;
	}

	@Override
	public BitSet getP2Set() {
		if (isCondition()) {
			return null;
		}
		if (isObject() || isStrConstObj() || isLibCallObj()) {
			return ovar.getP2Set();
		}
		return svar.getP2Set();
	}

	@Override
	public Local getBaseLocal() {
		if (isCondition()) {
			return null;
		}
		if (isObject() || isStrConstObj() || isLibCallObj()) {
			return ovar.getBaseLocal();
		}
		return svar.getBaseLocal();
	}
	
} // definition of CDEdgeVar

/* vim :set ts=4 tw=4 tws=4 */
