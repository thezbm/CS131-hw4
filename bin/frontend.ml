open Ll
open Llutil
open Ast

(* This file is where much of the work of the project will be carried out.
   Follow the instructions on the project web site, but first skim through
   this file to see what it contains.
*)


(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements that will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for
     compiling local variable declarations
*)

type elt =
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

(* The type of streams of LLVMLite instructions. Note that to improve performance,
 * we will emit the instructions in reverse order. That is, the LLVMLite code:
 *     %1 = mul i64 2, 2
 *     %2 = add i64 1, %1
 *     br label %l1
 * would be constructed as a stream as follows:
 *     I ("1", Binop (Mul, I64, Const 2L, Const 2L))
 *     >:: I ("2", Binop (Add, I64, Const 1L, Id "1"))
 *     >:: T (Br "l1")
 *)
type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None ->
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator"
    | Some term ->
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  let lookup_opt (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    List.assoc_opt id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_opt (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None

end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) ->
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearerhw, I may do that for next time around.]]


   Consider globals7.oat (in hw4programs)

   /--------------- globals7.oat ------------------
   global arr = int[] null;

   int foo() {
     var x = new int[3];
     arr = x;
     x[2] = 3;
     return arr[2];
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has
       the same type as @arr

   (2) @oat_alloc_array allocates len+1 i64's

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7

   (4) stores the resulting array value (itself a pointer) into %_x7

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed
      to by %_x7

  (6) store the array value (a pointer) into @arr

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] },
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr

  (11)  calculate the array index offset

  (12) load the array value at the index

*)

(* Global initialized arrays:

  There is another wrinkle: to compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* )
  @_global_arr5 = global { i64, [4 x i64] }
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*)



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]




(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression.

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with

  | CNull rty -> cmp_ty (TRef rty), Null, []

  | CBool b -> I1, Const (if b then 1L else 0L), []

  | CInt i -> I64, Const i, []

  | CStr s ->
    let gid = gensym "cstr" in
    let size = String.length s + 1 in
    Ptr I8, Gid gid, [G (gid, (Array (size, I8), GString s))]

  | CArr (ty, es) ->
    let ll_elem_ty = cmp_ty ty in
    let size = List.length es in
    let arr_ty, arr_op, alloc_stream = oat_alloc_array ty (Const (Int64.of_int size)) in
    (* Create a temporary array ptr for value assignment. *)
    let arr_ptr_tmp_id = gensym "array_ptr_temp" in
    let init_stream = lift [
      arr_ptr_tmp_id, Alloca arr_ty;
      "", Store (arr_ty, arr_op, Id arr_ptr_tmp_id)
    ] in
    let c' = Ctxt.add c arr_ptr_tmp_id (Ptr arr_ty, Id arr_ptr_tmp_id) in
    let store_stream =
      List.mapi
        (fun i e ->
          let _, s = cmp_stmt c' Void Ast.(
            no_loc (Assn (
              no_loc (Index (
                no_loc (Id arr_ptr_tmp_id), no_loc (CInt (Int64.of_int i))
              )),
              e)
            )
          ) in s)
        es
      |> List.concat
    in
    arr_ty, arr_op, alloc_stream >@ init_stream >@ store_stream

  | NewArr (ty, e) ->
    let _, size_op, size_stream = cmp_exp c e in
    let alloc_ty, alloc_op, alloc_code = oat_alloc_array ty size_op in
    alloc_ty, alloc_op, size_stream >@ alloc_code

  (* We map oat variables only to llvm Ids or Gids in the ctxt.
     The Ids for local variables are alloca'd, so both Ids and Gids
     should have pointer types.
  *)
  | Id _
  (* NOTE: `var a = int[3][2];` is invalid in this implementation. *)
  | Index _ ->
    let ty, op, stream = cmp_lhs c exp in
    let t = begin
      match ty with
      | Ptr t -> t
      | _ -> failwith "cmp_exp: invalid Id type"
    end in
    let id = gensym "loaded_var" in
    t, Id id, stream >@ [I (id, Load (ty, op))]

  | Call (f, args) ->
    let ret_ty, ret_op = match f.elt with
      | Id x -> Ctxt.lookup_function x c
      | _ -> failwith "cmp_exp: invalid function call"
    in
    let arg_tys, arg_ops, arg_code = List.fold_right
      (fun arg (tys, ops, codes) ->
        let ty, op, code = cmp_exp c arg in
        ty::tys, op::ops, code >@ codes
      ) args ([], [], []) in
    let ret_ty = match ret_ty with
      | Ptr (Fun (_, t)) -> t
      | _ -> failwith "cmp_exp: invalid function type" in
    let ret_id = gensym "call" in
    ret_ty, Id ret_id,
    arg_code
    >:: I (ret_id, Call (ret_ty, ret_op, List.combine arg_tys arg_ops))

  | Uop (op, e) ->
    let t, ll_op, code = cmp_exp c e in
    let ll_inst = match op with
    | Neg -> Binop (Sub, I64, Const 0L, ll_op)
    | Lognot -> Icmp (Eq, I1, ll_op, Const 0L)
    | Bitnot -> Binop (Xor, I64, ll_op, Const (-1L))
    in
    let ret_id = gensym "uop" in
    t, Id ret_id, code >@ [I (ret_id, ll_inst)]

  | Bop (op, e1, e2) ->
    let ll_t1, op1, code1 = cmp_exp c e1 in
    let ll_t2, op2, code2 = cmp_exp c e2 in
    let ast_t1, ast_t2, ast_t3 = typ_of_binop op in
    let ll_t3 = cmp_ty ast_t3 in
    if ll_t1 <> cmp_ty ast_t1 || ll_t2 <> cmp_ty ast_t2 || ll_t1 <> ll_t2
    then
      Printf.sprintf
        "cmp_exp: invalid binary operation: %s %s %s"
        (Llutil.string_of_ty ll_t1)
        (Llutil.string_of_ty ll_t2)
        (Llutil.string_of_ty ll_t3)
      |> failwith;
    let ll_inst = match op with
    | Add -> Binop (Add, ll_t1, op1, op2)
    | Sub -> Binop (Sub, ll_t1, op1, op2)
    | Mul -> Binop (Mul, ll_t1, op1, op2)
    | Eq ->  Icmp (Eq, ll_t1, op1, op2)
    | Neq -> Icmp (Ne, ll_t1, op1, op2)
    | Lt ->  Icmp (Slt, ll_t1, op1, op2)
    | Lte -> Icmp (Sle, ll_t1, op1, op2)
    | Gt ->  Icmp (Sgt, ll_t1, op1, op2)
    | Gte -> Icmp (Sge, ll_t1, op1, op2)
    | And -> Binop (And, ll_t1, op1, op2)
    | Or -> Binop (Or, ll_t1, op1, op2)
    | IAnd -> Binop (And, ll_t1, op1, op2)
    | IOr -> Binop (Or, ll_t1, op1, op2)
    | Shl -> Binop (Shl, ll_t1, op1, op2)
    | Shr -> Binop (Lshr, ll_t1, op1, op2)
    | Sar -> Binop (Ashr, ll_t1, op1, op2)
    in
    let ret_id = gensym "bop" in
    ll_t3, Id ret_id, code1 >@ code2 >@ [I (ret_id, ll_inst)]

and cmp_lhs (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with

  | Id x ->
    let ty, op = Ctxt.lookup x c in begin
      match ty, op with
      | Ptr _, Id _ | Ptr _, Gid _ ->
        ty, op, []
      | _ ->
        Printf.sprintf
          "cmp_exp: invalid Id type: %s, op: %s"
          (Llutil.string_of_ty ty)
          (Llutil.string_of_operand op)
        |> failwith
    end

  | Index (arr, idx) ->
    let arr_ptr_ty, arr_op, arr_code = cmp_lhs c arr in
    let idx_ty, idx_op, idx_code = cmp_exp c idx in
    let arr_ty = match arr_ptr_ty with
      | Ptr t -> t
      | _ -> failwith "cmp_lhs: invalid array ptr type"
    in
    let elem_ty = match arr_ty with
      | Ptr (Struct [I64; Array (0, t)]) -> t
      | _ -> failwith "cmp_lhs: invalid array type"
    in
    let arr_id = gensym "arr" in
    let elem_ptr_id = gensym "elem_ptr" in
    Ptr elem_ty, Id elem_ptr_id,
    arr_code >@ idx_code
    >:: I (arr_id, Load (Ptr arr_ty, arr_op))
    >:: I (elem_ptr_id, Gep (arr_ty, Id arr_id, [Const 0L; Const 1L; idx_op]))

  | Call (f, args) ->
    let ret_ty, ret_op, code = cmp_exp c exp in
    let ret_id = match ret_op with
    | Id x -> x
    | _ -> failwith "cmp_lhs: invalid ret operand"
    in
    let ret_ptr_id = gensym "ret_ptr" in
    Ptr ret_ty, Id ret_ptr_id,
    code
    >:: I (ret_ptr_id, Alloca ret_ty)
    >:: I ("", Store (ret_ty, Id ret_id, Id ret_ptr_id))

  | _ ->
    Printf.sprintf
      "cmp_lhs: invalid lhs: %s"
      (Astlib.string_of_exp exp)
    |> failwith

(* Compile a statement in context c with return typ rt. Return a new context,
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable
     declarations

   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)
and cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with

  | Assn (lhs, rhs) ->
    let lty, lop, lhs_code = cmp_lhs c lhs in
    let rty, rop, rhs_code = cmp_exp c rhs in
    let store = match lty with
      | Ll.Ptr t -> Store (t, rop, lop)
      | _ -> failwith "cmp_stmt: invalid assignment"
    in
    c, lhs_code >@ rhs_code >@ [I ("", store)]

  | Decl (id, e) ->
    (* We implement variable shadowing. *)
    let ll_id = gensym id in
    let ty, op, code = cmp_exp c e in
    let c' = Ctxt.add c id (Ll.Ptr ty, Ll.Id ll_id) in
    begin
      match ty with
      | Ll.I1 | Ll.I8 | Ll.I64 | Ll.Ptr _ | Ll.Struct _ ->
        c',
        code >@
        [ E (ll_id, Alloca ty)
        ; I (ll_id, Store (ty, op, Ll.Id ll_id))
        ]
      | Ll.Void | Ll.Array _ | Ll.Fun _ | Ll.Namedt _ ->
        failwith "cmp_stmt: invalid declaration"
    end

  | Ret e -> begin
      match rt, e with
      | Ll.Void, None ->
        (c, [T (Ret (Ll.Void, None))])
      | _, Some e ->
        let ty, op, code = cmp_exp c e in
        if ty <> rt then
          Printf.sprintf
            "cmp_stmt: invalid return value type: expected %s, got %s"
            (Llutil.string_of_ty rt)
            (Llutil.string_of_ty ty)
          |> failwith;
        c, code >@ [T (Ret (rt, Some op))]
      | _ ->
        failwith "cmp_stmt: invalid return statement"
    end

  | SCall (f, args) ->
    let _, _, code = cmp_exp c (no_loc (Ast.Call (f, args))) in
    c, code

  | If (cond, thn, els) ->
    (* If has its own ctxt scope. *)
    c, cmp_if c rt cond thn els

  | While (cond, body) ->
    (* While has its own ctxt scope. *)
    c, cmp_while c rt cond body

  | For (vdecls, cond, updt, body) ->
    (* For has its own ctxt scope. *)
    c, cmp_for c rt vdecls cond updt body

and cmp_if
  (c : Ctxt.t)
  (rt : Ll.ty)
  (cond : Ast.exp node)
  (thn : Ast.block)
  (els : Ast.block)
  : stream
  =
  let _cond_ty, cond_op, cond_code = cmp_exp c cond in
  let _thn_c, thn_code = cmp_block c rt thn in
  let _els_c, els_code = cmp_block c rt els in
  let then_lbl = gensym "then" in
  let else_lbl = gensym "else" in
  let end_lbl = gensym "end" in
  let stream =
    cond_code
    >:: (T (Cbr (cond_op, then_lbl, else_lbl)))
    >:: (L then_lbl)
    >@ thn_code
    >:: (T (Br end_lbl))
    >:: (L else_lbl)
    >@ els_code
    >:: (T (Br end_lbl))
    >:: (L end_lbl) in
  stream

and cmp_while
  (c:Ctxt.t)
  (rt:Ll.ty)
  (cond:Ast.exp node)
  (body:Ast.block)
  : stream
  =
  let _cond_ty, cond_op, cond_code = cmp_exp c cond in
  let _body_c, body_code = cmp_block c rt body in
  let loop_lbl = gensym "loop" in
  let end_lbl = gensym "end" in
  let body_lbl = gensym "body" in
  []
  >:: T (Br loop_lbl)
  >:: L loop_lbl
  >@ cond_code
  >:: T (Cbr (cond_op, body_lbl, end_lbl))
  >:: L body_lbl
  >@ body_code
  >:: T (Br loop_lbl)
  >:: L end_lbl

and cmp_for
  (c : Ctxt.t)
  (rt : Ll.ty)
  (vdecls : Ast.vdecl list)
  (cond : Ast.exp node option)
  (updt : Ast.stmt node option)
  (body : Ast.block)
  : stream
  =
  let cond = match cond with
    | Some cond -> cond
    | None -> CBool true |> no_loc
  and updt = match updt with
    | Some updt -> [updt]
    | None -> []
  in
  (
    List.map (fun (x) -> Decl x |> no_loc) vdecls
    @
    [ While (cond, body @ updt) |> no_loc ]
  )
  |> cmp_block c rt
  |> snd


(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s ->
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c, []) stmts



(* Adds each function identifier to the context at an
   appropriately translated type.

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.fold_left (fun c -> function
    | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
        let ft = TRef (RFun (List.map fst args, frtyp)) in
        Ctxt.add c fname (cmp_ty ft, Gid fname)
    | _ -> c
  ) c p

(* Populate a context with bindings for global variables
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C).
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.fold_left (fun c -> function
    | Ast.Gvdecl { elt={ name; init } } ->
      let ty = init.elt |> (function
        | CNull rty -> TRef rty
        | CBool _ -> TBool
        | CInt _ -> TInt
        | CStr _ -> TRef RString
        | CArr (ty, _) -> TRef (RArray ty)
        | _ -> failwith "cmp_global_ctxt: invalid initializer"
      )
      |> cmp_ty
      (* All global variables are treated as pointers. *)
      |> (fun t -> Ptr t)
      in
      Ctxt.add c name (ty, Gid name)
    | _ -> c
  ) c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from
*)
let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let { frtyp; fname; args; body } = f.elt in

  let ret_ll_type = match frtyp with
    | RetVoid -> Void
    | RetVal ty -> cmp_ty ty in

  let args_ast_types, args_ids = args |> List.split in
  (* Create new ids for args to be used in the function. *)
  let args_ids' = List.map (fun _ -> gensym "arg") args in
  let args_ll_types = List.map cmp_ty args_ast_types in
  let f_ll_type = (args_ll_types, ret_ll_type) in

  (* Allocate stack space for function parameters and fill their values. *)
  let alloca_store_stream = List.concat_map (fun ((ty, id), id') ->
    lift [
      id', Alloca (cmp_ty ty);
      "", Store (cmp_ty ty, Id id, Id id');
    ]) (List.combine args args_ids') in

  (* Add args to context with their new ids. *)
  let c = List.fold_left2 (fun c (ty, id) id' ->
    (* All alloca'd variables are treated as pointers. *)
    Ctxt.add c id (Ptr (cmp_ty ty), Id id')
  ) c args args_ids' in

  let c, body_stream = cmp_block c ret_ll_type body in
  (* Need a default return at the end of the function to satisfy llvm. *)
  let default_ret = match ret_ll_type with
    | Void -> None
    | I1 | I64 -> Some (Const 0L)
    | Ptr _ -> Some Null
    | _ -> failwith "cmp_fdecl: invalid return type" in
  let stream =
    alloca_store_stream >@
    body_stream >@
    [T (Ret (ret_ll_type, default_ret))] in
  let f_cfg, gdecls = cfg_of_stream stream in

  { f_ty=f_ll_type; f_param=args_ids; f_cfg=f_cfg }, gdecls


(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)
let rec cmp_gexp (c:Ctxt.t) (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull rty -> (cmp_ty (TRef rty), GNull), []
  | CBool b -> (cmp_ty TBool, GInt (if b then 1L else 0L)), []
  | CInt i -> (cmp_ty TInt, GInt i), []
  | CStr s ->
    let typ = cmp_ty (TRef RString)
    and size = String.length s + 1 in
    let raw_typ = Ll.Array (size, I8)
    and raw_gid = gensym "gstring_raw" in
      (typ, GBitcast (
        Ptr raw_typ,
        GGid raw_gid, typ
      )),
      [raw_gid, (raw_typ, GString s)]
  | CArr (ty, es) ->
    let ginits, gid_gdecls = List.split (List.map (cmp_gexp c) es) in
    let typ = cmp_ty (TRef (RArray ty))
    and size = List.length ginits in
    let raw_typ = Struct [I64; Array (size, cmp_ty ty)]
    and raw_gid = gensym "garray_raw" in
      (typ, GBitcast (
        Ptr raw_typ,
        GGid raw_gid, typ
      )),
      (raw_gid, (raw_typ, GStruct [
        I64, GInt (Int64.of_int size);
        Array (size, cmp_ty ty), GArray ginits
      ])) :: (List.concat gid_gdecls)
  | _ -> failwith "cmp_gexp: invalid initializer"


(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt =
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls =
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } ->
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }

