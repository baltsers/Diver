import java.lang.reflect.Method;


public class AllDriversMain {
	static void __link() {
		// added by hcai for Soot static-analysis phase
		EAS.Monitor.__link();
		Diver.EAMonitor.__link();
	}
	public static void main(String[] args) throws Exception {
		// Get test driver's class
		final String testdriverClassName = args[0];
		Class testDriverCls = Class.forName(testdriverClassName);

		// Prepare remaining args array for test driver
		String[] argsToTD = new String[args.length - 1];
		for (int i = 0; i < args.length - 1; ++i)
			argsToTD[i] = args[i+1];

		try {
		// Get test driver's main method and invoke it
		Class[] mainParms = new Class[] { String[].class };
		Method tdMain = testDriverCls.getDeclaredMethod("main", mainParms);
		Object[] invArgs = new Object[] { argsToTD };
		try { tdMain.invoke(null, invArgs); } catch (Exception e) { e.printStackTrace(); }

		}
		catch (Exception e) { e.printStackTrace(); }

		// force inclusion of all test drivers and the nanoxml methods they invoke
		if (args.length == 0) {  // make sure this body is not called!
			     if (args.length == 0) AddChild1_wy_v1.main(argsToTD);
			else if (args.length == 0) AddChild2_wy_v1.main(argsToTD);
			else if (args.length == 0) AddChild3_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckAttr1_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckAttr2_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckAttr3_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckAttr4_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckAttr5_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckChildren1_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckChildren2_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckChildren3_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckLeaf1_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckLeaf2_wy_v1.main(argsToTD);
			else if (args.length == 0) CheckLeaf3_wy_v1.main(argsToTD);
			else if (args.length == 0) CrElement1_wy_v1.main(argsToTD);
			else if (args.length == 0) CrElement2_wy_v1.main(argsToTD);
			else if (args.length == 0) CrElement3_wy_v1.main(argsToTD);
			else if (args.length == 0) Parser1_vw_v0.main(argsToTD);
			else if (args.length == 0) Parser1_vw_v1.main(argsToTD);
			else if (args.length == 0) Parser2_vw_v0.main(argsToTD);
			else if (args.length == 0) Parser2_vw_v1.main(argsToTD);
			else if (args.length == 0) Parser3_vw_v0.main(argsToTD);
			else if (args.length == 0) Parser3_vw_v1.main(argsToTD);
			else if (args.length == 0) Parser4_vw_v0.main(argsToTD);
			else if (args.length == 0) Parser4_vw_v1.main(argsToTD);
			else if (args.length == 0) Parser5_vw_v0.main(argsToTD);
			else if (args.length == 0) Parser5_vw_v1.main(argsToTD);
			else if (args.length == 0) Parser6_vw_v0.main(argsToTD);
			else if (args.length == 0) Parser6_vw_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal1_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal2_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal3_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal4_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal5_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal6_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal7_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal8_wy_v1.main(argsToTD);
			else if (args.length == 0) RAttrVal9_wy_v1.main(argsToTD);
			else if (args.length == 0) RChildAtIndex1_wy_v1.main(argsToTD);
			else if (args.length == 0) RChildAtIndex2_wy_v1.main(argsToTD);
			else if (args.length == 0) RChildAtIndex3_wy_v1.main(argsToTD);
			else if (args.length == 0) RChildAtIndex4_wy_v1.main(argsToTD);
			else if (args.length == 0) RChildCount_wy_v1.main(argsToTD);
			else if (args.length == 0) RContent_wy_v1.main(argsToTD);
			else if (args.length == 0) REleName_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveAttr1_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveAttr2_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveChild1_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveChild2_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveChild3_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveChildIndex1_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveChildIndex2_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveChildIndex3_wy_v1.main(argsToTD);
			else if (args.length == 0) RemoveChildIndex4_wy_v1.main(argsToTD);
			else if (args.length == 0) REnumAttr_wy_v1.main(argsToTD);
			else if (args.length == 0) REnumChildren_wy_v1.main(argsToTD);
			else if (args.length == 0) RFirstChild1_wy_v1.main(argsToTD);
			else if (args.length == 0) RFirstChild2_wy_v1.main(argsToTD);
			else if (args.length == 0) RFirstChild3_wy_v1.main(argsToTD);
			else if (args.length == 0) RFirstChild4_wy_v1.main(argsToTD);
			else if (args.length == 0) RPropAttr_wy_v1.main(argsToTD);
			else if (args.length == 0) RVecChildNamed1_wy_v1.main(argsToTD);
			else if (args.length == 0) RVecChildNamed2_wy_v1.main(argsToTD);
			else if (args.length == 0) RVecChildNamed3_wy_v1.main(argsToTD);
			else if (args.length == 0) RVecChildren_wy_v1.main(argsToTD);
			else if (args.length == 0) SetAttr1_wy_v1.main(argsToTD);
			else if (args.length == 0) SetAttr2_wy_v1.main(argsToTD);
			else if (args.length == 0) SetAttr3_wy_v1.main(argsToTD);
			else if (args.length == 0) SetAttr4_wy_v1.main(argsToTD);
			else if (args.length == 0) SetCont1_wy_v1.main(argsToTD);
			else if (args.length == 0) SetCont2_wy_v1.main(argsToTD);
			else if (args.length == 0) SetEleName1_wy_v1.main(argsToTD);
			else if (args.length == 0) SetEleName2_wy_v1.main(argsToTD);
			else if (args.length == 0) Writer1_wy_v1.main(argsToTD);
			else if (args.length == 0) Writer2_wy_v1.main(argsToTD);
			else if (args.length == 0) Writer3_wy_v1.main(argsToTD);
			else if (args.length == 0) Writer4_wy_v1.main(argsToTD);
			else if (args.length == 0) Writer5_wy_v1.main(argsToTD);
			else if (args.length == 0) Writer6_wy_v1.main(argsToTD);
		}
	}
}
