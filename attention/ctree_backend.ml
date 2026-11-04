(* Unverified MLIR/JSON elaboration only. All SSA evaluation and region/loop
   execution is in extracted [E.execute]. No Runner.execute_* is called here. *)
module E = Extracted_semantics.Unified_semantics
open Parser
exception Unsupported of string
exception Budget_exhausted
exception Deadlock
let unsupported op = raise (Unsupported op.opcode)
let attr op key = match List.assoc_opt key op.attributes with
 | Some x -> x | None -> Source.fail op.span ("missing attribute " ^ key)
let flag op key = List.assoc_opt key op.attributes = Some (`Bool true)
let shaped op = match op.result_type with Some (ShapedType (_,s,t)) -> s,t
 | _ -> Source.fail op.span "expected shaped result"
let scalar op = match op.result_type with Some (ScalarType t) -> t
 | _ -> Source.fail op.span "expected scalar result"
let nats op key = Yojson.Safe.Util.(attr op key |> to_list |> List.map to_int)
let float_literal s =
 let x = if String.starts_with ~prefix:"0x" s then Int32.float_of_bits (Int32.of_string s)
 else float_of_string s in
 if Float.is_nan x then E.NotANumber else if x = infinity then E.PositiveInfinity
 else if x = neg_infinity then E.NegativeInfinity
 else let q = Q.of_float x in E.FiniteFloat {E.qnum=Numeric.z_of_big (Q.num q);
 qden=Numeric.positive_of_big (Q.den q)}
type compiled = { body : E.program; name : string -> int; locations : (int * operation) list }
let compile (p : Parser.program) =
 let names = Hashtbl.create 64 and next_name = ref 0 and locations = ref [] and next_loc = ref 0 in
 let name s = match Hashtbl.find_opt names s with Some i -> i | None ->
  let i = !next_name in incr next_name; Hashtbl.add names s i; i in
 let index = function Static n -> E.Literal (Numeric.z_of_int n) | Dynamic s -> E.SSAIndex (name s) in
 let indices op key = Yojson.Safe.Util.(attr op key |> to_list) |> List.map (fun x -> index (Parser.index_expr x)) in
 let rec block = function
 | [] -> E.PDone
 | (op : operation)::rest ->
  let loc = !next_loc in incr next_loc; locations := (loc,op)::!locations;
  let ns = List.map name op.operands in
  let one () = match ns with [a] -> a | _ -> unsupported op in
  let two () = match ns with [a;b] -> a,b | _ -> unsupported op in
  let first () = match ns with a::_ -> a | _ -> unsupported op in
  let decl () = let sh,_ = shaped op in List.map Numeric.z_of_int sh in
  let dst () = match op.outputs with [x] -> name x | _ -> unsupported op in
  let unary_input () = match op.inputs with [x] -> name x | _ -> unsupported op in
  let binary_input () = match op.inputs with [a;b] -> name a,name b | _ -> unsupported op in
  match op.opcode with
  | "func.return" | "scf.yield" -> if ns <> [] then unsupported op; E.PDone
  | "scf.if" ->
    if op.result <> None || op.region_arguments <> [] then unsupported op;
    E.PIf (loc,one (),block op.region,block op.else_region,block rest)
  | "scf.for" ->
    (match ns,op.region_arguments with
    | [lo;hi;step],[(iv,_)] when op.result = None ->
       E.PFor (loc,name iv,lo,hi,step,block op.region,block rest)
    | _ -> unsupported op)
  | _ ->
   if op.region <> [] || op.else_region <> [] then unsupported op;
   let atom = match op.opcode with
   | "arith.constant" -> let ty = scalar op in
     (match attr op "value" with `Int n -> E.AInt (ty,Numeric.z_of_int n)
     | `String s when ty = E.Float32Type -> E.AFloat (ty,float_literal s)
     | _ -> unsupported op)
   | "arith.addi" | "arith.subi" | "arith.muli" | "arith.maxsi" | "arith.minsi"
   | "arith.divsi" | "arith.remsi" -> let a,b = two () in
     let oper = match op.opcode with "arith.addi" -> E.ArithAddI | "arith.subi" -> E.ArithSubI
      | "arith.muli" -> E.ArithMulI | "arith.maxsi" -> E.ArithMaxSI | "arith.minsi" -> E.ArithMinSI
      | "arith.divsi" -> E.ArithDivSI | _ -> E.ArithRemSI in
     E.AInteger (oper,scalar op,a,b)
   | "arith.cmpi" -> let a,b = two () in E.ACompare (Yojson.Safe.Util.to_int (attr op "predicate"),a,b)
   | "arith.index_cast" | "arith.extsi" -> E.ACast
     ((if op.opcode = "arith.extsi" then E.ArithExtSI else E.ArithIndexCast),scalar op,one ())
   | "tensor.empty" -> let sh,ty = shaped op in E.AEmpty (sh,ty)
   | "memref.alloc" -> let sh,ty = shaped op in E.AAlloc (E.ASDefault,sh,ty)
   | "memref.reinterpret_cast" ->
     let off = match attr op "offsets" with `List [`String s] ->
      if String.starts_with ~prefix:"%" s then E.SSAIndex (name s)
      else E.Literal (Numeric.z_of_big (Numeric.Big.of_string s)) | _ -> unsupported op in
     E.AReinterpret (first (),off,nats op "sizes",List.map Numeric.z_of_int (nats op "strides"))
   | "memref.subview" -> E.ASubview (first (),indices op "offsets",indices op "sizes",indices op "strides",decl ())
   | "tensor.extract_slice" -> E.ASlice (first (),indices op "offsets",indices op "sizes",indices op "strides",decl ())
   | "bufferization.to_tensor" -> E.AToTensor (one (),{E.access_restrict=flag op "restrict";access_writable=flag op "writable"})
   | "memref.copy" -> let a,b = two () in E.ACopy (a,b)
   | "bufferization.materialize_in_destination" -> let a,b = two () in E.AStore (a,b,flag op "writable")
   | "linalg.fill" | "hivm.hir.vbrc" ->
     if op.opcode = "hivm.hir.vbrc" && List.mem_assoc "broadcast_dims" op.attributes && nats op "broadcast_dims" <> [] then unsupported op;
     E.AFill (op.opcode = "hivm.hir.vbrc",unary_input (),dst ())
   | "linalg.elemwise_binary" | "hivm.hir.vadd" ->
     if op.opcode = "linalg.elemwise_binary" && Yojson.Safe.Util.(attr op "fun" |> member "value" |> to_string) <> "add" then unsupported op;
     let a,b = binary_input () in E.AAdd (op.opcode = "hivm.hir.vadd",a,b,dst ())
   | _ -> unsupported op in
   E.PAtom (loc,Option.map name op.result,atom,block rest)
 in let body = block p.body in {body;name;locations= !locations}
let value = function
 | Runner.Int (ty,z) -> E.SVInt (ty,z) | Runner.Float (ty,x) -> E.SVFloat (ty,x)
 | Runner.Tensor t -> E.SVTensor t | Runner.View v -> E.SVView v
 | Runner.Memref (id,sh,ty) -> E.SVMemref (id,sh,ty)
let run (ctx : Runner.context) ~budget compiled env =
 let env = List.map (fun (n,v) -> compiled.name n,value v) env in
 let ((status,memory),log),remaining = E.execute_budget Numeric.scalar Numeric.hivm
   !budget 1000000 compiled.body env (!(ctx.state)).memory in
 budget := remaining;
 ctx.state := {!(ctx.state) with Handlers.memory};
 List.iter (fun loc ->
  let op = List.assoc loc compiled.locations in
  ctx.steps <- ctx.steps + 1;
  ctx.trace (`Assoc ["backend",`String "ctree";"program_id",`Int ctx.pid;
    "opcode",`String op.opcode;"file",`String op.span.file;"line",`Int op.span.start.line])) log;
 match status with E.Finished _ -> ()
 | E.Unsupported -> raise (Unsupported "Rocq operation")
 | E.BudgetExhausted -> raise Budget_exhausted | E.Deadlock -> raise Deadlock
 | E.SemanticError e -> raise (Handlers.Semantic_error e)
