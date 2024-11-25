open Util.Assert
open Gradedtests

(* You should add additional test cases here to help you   *)
(* debug your program.                                          *)

(* NOTE: Your "submitted public test case" belongs over in the 
   shared git submodule.   
*)

let my_tests = [
  (* This program calculates pi. *)
  ("test/studentprograms/pi.oat", "", "pi is 3141396/1000000. exited with 0");
]

let provided_tests : suite = [
  Test("my tests", executed_oat_file my_tests)
] 
