# HW4: Oat v.1

Quick Start:

1. open the folder in VSCode
2. start an OCaml sandbox terminal
3. run `make test` from the command line
4. open `bin/frontend.ml`

See the general toolchain and project instructions on the course web site. The
course web pages have a link to the html version of the homework instructions.


Using ``oatc``
--------------

``oatc`` acts like the clang compiler.  Given several .oat, .ll, .c, and .o
files, it will compile the .oat and .ll files to .s files (using the CIS 341
frontend and backend) and then combine the results with the .c and .o files to
produce an executable named a.out.  You can also compile the .ll files using
clang instead of the CS131 backend, which can be useful for testing purposes.


* To run the automated test harness do:

        ./oatc --test

* To compile oat files using the 341 backend:

        ./oatc path/to/foo.oat

  - creates output/foo.ll  frontend ll code
  - creates output/foo.s   backend assembly code
  - creates output/foo.o   assembled object file
  - creates a.out          linked executable

 NOTE: by default the .s and .o files are created in 
 a directory called output, and the filenames are 
 chosen so that multiple runs of the compiler will
 not overwrite previous outputs.  foo.ll will be 
 compiled first to foo.s then foo_1.s, foo_2.s, etc.


* To compile oat files using the clang backend:

        ./oatc --clang path/to/foo.oat

* Useful flags:

  | Flag              | Description                                                                                       |
  |-------------------|---------------------------------------------------------------------------------------------------|
  | --print-oat       | pretty prints the Oat abstract syntax to the terminal                                             |
  | --print-ll        | echoes the ll program to the terminal                                                             |
  | --print-x86       | echoes the resulting .s file to the terminal                                                      |
  | --interpret-ll    | runs the ll file through the reference interpreter and outputs the results to the console         |
  | --execute-x86     | runs the resulting a.out file natively (applies to either the 341 backend or clang-compiled code) |
  | --clang           | compiles to assembly using clang, not the 341 backend                                             |
  | -v                | generates verbose output, showing which commands are used for linking, etc.                       |
  | -op ``<dirname>`` | change the output path [DEFAULT=output]                                                           |
  | -o                | change the generated executable's name [DEFAULT=a.out]                                            |
  | -S                | stop after generating .s files                                                                    |
  | -c                | stop after generating .o files                                                                    |
  | -h or --help      | display the list of options                                                                       |


* Example uses:

Run the test case hw4programs/fact.oat using the 341 backend:

          /oatc --execute-x86 hw4programs/fact.oat bin/runtime.c 
          120--------------------------------------------------------------- Executing: a.out
          * a.out returned 0
