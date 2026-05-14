# Diver

**Hybrid Program Dependence Approximation for Effective Dynamic Impact Prediction**

| | |
|---|---|
| Original artifact | <http://chapering.github.io/projects/diver/> |
| Imported from | the publications page |
| Tool | `pubs2github` |


## Other papers sharing this artifact

- DiaPro: Unifying Dynamic Impact Analyses for Improved and Variable Cost-Effectiveness
- A Framework for Cost-effective Dependence-based Dynamic Impact Analysis
- Diver: Precise Dynamic Impact Analysis Using Dependence-based Trace Pruning

---

## Contents

The artifact contains 314 file(s) including Java, C/C++, Config files, and Documentation.

```
├── mcia_release
│   ├── libs
│   │   ├── duaf.jar
│   │   ├── jasminclasses-2.3.0.jar
│   │   ├── java_cup.jar
│   │   ├── polyglot.jar
│   │   ├── rt.jar
│   │   └── sootclasses-2.3.0.jar
│   ├── src
│   │   ├── Diver
│   │   ├── EAS
│   │   └── MciaUtil
│   └── build.xml
├── Nano.tdv1
│   ├── inputs
│   │   └── testinputs.txt
│   ├── inputs-lnx
│   │   ├── database.xml
│   │   ├── database_sc_1.xml
│   │   ├── double_dtd.xml
│   │   ├── emptyelem1_wy.xml
│   │   ├── emptyelem2_wy.xml
│   │   ├── emptyelem3_wy.xml
│   │   ├── emptyfile_sc_2.xml
│   │   ├── file10_wy.xml
│   │   ├── file11_wy.xml
│   │   ├── file12_wy.xml
│   │   ├── file1_wy.xml
│   │   ├── file2_wy.xml
│   │   ├── file3_wy.xml
│   │   ├── file4_wy.xml
│   │   ├── file5_wy.xml
│   │   ├── file6_wy.xml
│   │   ├── file7_wy.xml
│   │   ├── file8_wy.xml
│   │   ├── file9_wy.xml
│   │   ├── include.ent
│   │   ├── internal_dtd.xml
│   │   ├── manydbnames_sc_3.xml
│   │   ├── manydbversions_sc_4.xml
│   │   ├── manyfielddefaults_sc_5.xml
│   │   ├── manyfielddesc_sc_6.xml
│   │   ├── manyfieldlength_sc_7.xml
│   │   ├── manyfieldnames_sc_8.xml
│   │   ├── manyfieldtypes_sc_9.xml
│   │   ├── manyindexnames_sc_10.xml
│   │   ├── manyindexref_sc_11.xml
│   │   ├── manyindextypes_sc_12.xml
│   │   ├── manytabledesc_sc_13.xml
│   │   ├── manytablenames_sc_14.xml
│   │   ├── ModifyList
│   │   ├── namespaces.xml
│   │   ├── nodbname_sc_15.xml
│   │   ├── nofieldnames_sc_16.xml
│   │   ├── nofieldtypes_sc_17.xml
│   │   ├── noindexcolumns_sc_18.xml
│   │   ├── noindextypes_sc_19.xml
│   │   ├── notablefields_sc_20.xml
│   │   ├── notablenames_sc_21.xml
│   │   ├── notables_sc_22.xml
│   │   … (157 more items)
│   … (242 more items)
… (329 more items)
```

---

## Original `README.txt` (from the upstream artifact)

========================================================
1. About This Project
---------------------
Diver is a method-level dynamic impact-analysis tool which combines an approximate statement-level 
static program dependence analysis and a dynamic analysis using method-execution events to predict 
runtime impacts of a given query (method).

The Diver project webpage is http://www3.nd.edu/~hcai/diver/.

2. Contents
---------------------
This package is created to demonstrate how to deploy and use Diver, including the following three directories:

mcia_release: the Diver source code in "src", with library dependencies in "libs"; Also, as a technique used 
as the baseline to compare Diver with, EAS is an earlier dynamic-impact-analysis tool computing runtime impacts 
purely based on method execution order.  
(details on EAS can be found in this paper http://dl.acm.org/citation.cfm?id=1062534).

NanoXML and Nano.tdv1: the library and test driver (with test suite) of the NanoXML project, which is used as 
a subject program under analysis for demonstrating the use of Diver.

3. Build/Install/Use
---------------------
The Ant build file (build.xml) is located under 'mcia_release', which has following main targets (with descriptions):

 cleanall     Clean up all that are generated
 diver_inst   Instrument the example subject NanoXML with Diver
 diver_query  Get the impact set of an example query from Diver
 diver_run    Run Diver-instrumented code to produce method traces used by Diver
 eas_inst     Instrument the example subject NanoXML with EAS
 eas_query    Get the impact set of an example query from EAS
 eas_run      Run EAS-instrumented code to produce method traces used by EAS

(These targets can be retrieved by running 'ant -p' in the 'mcia_release' directory as well.)

To compile Diver and the example subject NanoXML, use 'ant build'.

Both techniques (Diver and EAS) work in three phases, static analysis, runtime, and post-processing, for which three 
targets, 'diver/eas_inst', 'diver/eas_run', and 'diver/eas_query' can be used, respectively.

========================================================
Should you encounter any issues when using this package, 
please email to hcai@nd.edu.

