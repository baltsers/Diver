# Diver

Project artifact for:

**Hybrid Program Dependence Approximation for Effective Dynamic Impact Prediction**

- Original artifact URL: <http://chapering.github.io/projects/diver/>
- Imported via `pubs2github` from the publications page
- Downloader: `page` — Downloaded 4 asset(s) linked from project page


## Other papers using the same artifact

- DiaPro: Unifying Dynamic Impact Analyses for Improved and Variable Cost-Effectiveness
- A Framework for Cost-effective Dependence-based Dynamic Impact Analysis
- Diver: Precise Dynamic Impact Analysis Using Dependence-based Trace Pruning

This repository was created automatically. The contents under this
directory mirror what was downloaded from the original artifact link
above; refer to that source for the authoritative version, licensing,
and any updates.

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

