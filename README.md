This is an SSA/SSI compiler for BioScript.  It implements the ChemType type system.

# Requirements:
 
 1. ChemLibrary: 
    1. Download and build the artifact: https://github.com/lilott8/ChemLibrary
    2. In the `project structure->modules` window, add a new `JARS or directories...` dependency and add the `chemlibrary.jar` to it for `compile`
 2. ChemTrails:
    1. Download and build the artifact: https://github.com/lilott8/ChemTrails
    2. In the `project structure->modules` window, add a new `JARS or directories...` dependency and add the `chemtrails.jar` to it for `compile`
 3. Installation of Z3 dependency:
    1. Install z3 from: `source`: https://github.com/Z3Prover/z3 or from `binary`: https://github.com/Z3Prover/z3/releases (preferred binary)
    2. In the `project structure->modules` window, add a new `JARS or directories...` dependency and add the `com.microsoft.z3.jar` to it for `compile`
    3. In the `run configuration` editor add an environment variable: `DYLD_LIBRARY_PATH` with the path: `/path/to/z3/*.dylib` files,
 
This is the minimum requirements to run the chemical compiler.
 
#Basic Usage

Chemical Compiler uses log4j for logging, so may provide a log4j xml config by: `-Dlog4j.configurationFile=/path/to/xml` 

We provide a basic one for you in: `src/main/resources/log4j.xml`

The basic command line usage:

 - -c/-compile [file/to/compile.json]
 - -p/-phase [comma delimited list of phases to run]
   - current support:
     - inference
 - -o/-output [path/to/output/dir]
 - -t/-translator [comma delimited list of translators]*
    - current support:
      - mfsim
      - typesystem
 - -ssi [run the ssi algorithm]
 
*if using a translator, you must provide an output directory.

 