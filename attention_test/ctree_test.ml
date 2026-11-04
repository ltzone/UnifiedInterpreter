open Attention_runtime
module E = Extracted_semantics.Unified_semantics
let data result = match result.Kernel.outputs with [o] -> o.data | _ -> assert false
let () =
 List.iter (fun n ->
  let a = Array.init n (fun i -> float_of_int (i mod 31 - 15) /. 4.) in
  let b = Array.init n (fun i -> float_of_int (i mod 17 - 8) /. 8.) in
  let reference = Array.map2 (+.) a b in
  List.iter (fun stage ->
   let file = "../artifacts/kernel_IR/vector-add/" ^ stage ^ ".mlir" in
   let pids = Hashtbl.create 8 and fills = ref 0 in
   let trace = function `Assoc fs when List.assoc_opt "backend" fs = Some (`String "ctree") ->
     (match List.assoc_opt "program_id" fs with Some (`Int pid) -> Hashtbl.replace pids pid () | _ -> ());
     (match List.assoc_opt "opcode" fs with Some (`String ("linalg.fill" | "hivm.hir.vbrc")) -> incr fills | _ -> ())
    | _ -> () in
   let fresh = Vector_add.run ~backend:`CTree ~stage ~trace ~file a b |> data in
   let old = Vector_add.run ~backend:`Legacy ~stage ~file a b |> data in
   assert (fresh = reference && fresh = old);
   assert (Hashtbl.length pids = (n+255)/256);
   assert (!fills = if n mod 256 = 0 then 0 else 2);
   Printf.printf "CTree/%s n=%d: exact three-way equality, pids, tail branches PASS\n%!" stage n
  ) ["hfusion";"hivm"]
 ) [0;1;255;256;257;512;513;777];
 let file = "fixtures/dynamic_slices.mlir" in
 let bindings = ["%input",Kernel.Input (Array.init 8 float_of_int);"%out",Kernel.Output] in
 let fresh = Kernel.run ~backend:`CTree ~file bindings |> data in
 let old = Kernel.run ~backend:`Legacy ~file bindings |> data in
 assert (fresh = [|3.;5.|] && fresh = old);
 print_endline "CTree: nested strided views and both region directions PASS";
 List.iter (fun count ->
  let file = Printf.sprintf "fixtures/ctree_loop_%d.mlir" count in
  let bindings = ["%out",Kernel.Output] in
  let fresh = Kernel.run ~backend:`CTree ~file bindings |> data in
  let old = Kernel.run ~backend:`Legacy ~file bindings |> data in
  let expected = if count = 0 then [|0.;0.;0.;0.|] else [|7.;7.;7.;7.|] in
  assert (fresh = expected && fresh = old);
  Printf.printf "CTree: scf.for count=%d exact three-way equality PASS\n%!" count
 ) [0;4];
 (match Vector_add.run ~backend:`CTree ~max_steps:1
   ~file:"../artifacts/kernel_IR/vector-add/hivm.mlir" [|1.|] [|2.|] with
  | _ -> assert false | exception Ctree_backend.Budget_exhausted -> ());
 let p = Parser.parse ~file:"fixtures/ctree_loop_4.mlir"
   (Attention.read_file "fixtures/ctree_loop_4.mlir") in
 let op = List.hd p.body in
 (match Ctree_backend.compile {p with body=[{op with opcode="hivm.hir.sync"}]} with
 | _ -> assert false | exception Ctree_backend.Unsupported _ -> ());
 (* A live descriptor must see later writes, unlike an eager tensor snapshot. *)
 let fresh = Kernel.run ~backend:`CTree ~file:"fixtures/ctree_live_view.mlir"
   ["%out",Kernel.Output] |> data in
 let old = Kernel.run ~backend:`Legacy ~file:"fixtures/ctree_live_view.mlir"
   ["%out",Kernel.Output] |> data in
 assert (fresh = [|7.;7.|] && fresh = old);
 print_endline "CTree: budget, explicit Unsupported, live view alias PASS"

let () =
 let id,m = E.allocate_memref E.ASGM E.Float32Type [2] E.empty_memory in
 let partial = E.bind (E.write_tensor_coordinates id [[0];[1]] [1.;2.])
    (fun _ -> E.Return (E.Error E.NumericFailure)) in
 let (status,after),_ = E.run_tree 10 10 (E.transaction partial) m [] in
 assert (status = E.SemanticError E.NumericFailure && after == m);
 let old_state = ref {Handlers.memory=m;marker=73} in
 (match Handlers.run ~state:old_state ~on_call:ignore (fun () ->
   Effect.perform (Handlers.Memory ("rollback",partial))) with
 | _ -> assert false | exception Handlers.Semantic_error E.NumericFailure -> ());
 assert ((!old_state).memory == m);
 let (status,after),_ = E.run_tree 10 1 (E.transaction partial) m [] in
 assert (status = E.BudgetExhausted && after == m);
 let alloc_then_fail = E.PAtom (0,Some 1,E.AAlloc (E.ASUB,[2],E.Float32Type),
   E.PAtom (1,None,E.AUnsupported,E.PDone)) in
 let (status,after),_ = E.execute Numeric.scalar Numeric.hivm 20 10 alloc_then_fail [] m in
 assert (status = E.Unsupported && after.memory_next_allocation = m.memory_next_allocation + 1);
 List.iter (fun step ->
  let z = Numeric.z_of_int in
  let env = [0,E.SVInt (E.IndexType,z 0);1,E.SVInt (E.IndexType,z 4);2,E.SVInt (E.IndexType,z step)] in
  let (status,after),_ = E.execute Numeric.scalar Numeric.hivm 20 10
   (E.PFor (0,3,0,1,2,E.PDone,E.PDone)) env m in
  assert (status = E.SemanticError E.StaticProgramError && after == m)
 ) [0;-1];
 let (status,_),_ = E.execute Numeric.scalar Numeric.hivm 20 10
   (E.PIf (0,99,E.PDone,E.PDone,E.PDone)) [] m in
 assert (status = E.SemanticError E.StaticProgramError);
 print_endline "CTree: rollback, earlier commits, memory budget, invalid loops and SSA PASS"

let () =
 let file = "fixtures/ctree_loop_i32.mlir" in
 let fresh = Kernel.run ~backend:`CTree ~file ["%out",Kernel.Output] |> data in
 let old = Kernel.run ~backend:`Legacy ~file ["%out",Kernel.Output] |> data in
 assert (fresh = [|7.;7.;7.;7.|] && fresh = old);
 print_endline "CTree: i32 induction and index cast (compiled attention loop form) PASS"

let () =
 let file = "../artifacts/kernel_IR/vector-add/hivm.mlir" in
 let a n = Array.make n 1. and b n = Array.make n 2. in
 ignore (Vector_add.run ~backend:`CTree ~max_steps:80 ~file (a 256) (b 256));
 (match Vector_add.run ~backend:`CTree ~max_steps:80 ~file (a 512) (b 512) with
 | _ -> failwith "CTree budget reset between program IDs"
 | exception Ctree_backend.Budget_exhausted -> ());
 print_endline "CTree: one launch fits, two launches exhaust cumulative tree budget PASS"

let () =
 (* Result arity is checked after the transaction commits in both backends. *)
 let file = "fixtures/ctree_live_view.mlir" in
 let parsed = Parser.parse ~file (Attention.read_file file) in
 let alloc = List.find (fun (op : Parser.operation) -> op.opcode = "memref.alloc") parsed.body in
 let malformed = {alloc with result=None} in
 let state = ref {Handlers.memory=E.empty_memory;marker=73} in
 let ctx = {Runner.state;steps=0;max_steps=100;current=None;pid=0;calls=0;loops=[];trace=ignore} in
 (match Runner.with_handlers ctx (fun () -> Runner.execute_block ctx [] [malformed]) with
 | _ -> failwith "legacy accepted allocation without result"
 | exception Source.Error (_,message) -> assert (message = "operation result count mismatch"));
 let (status,after),_ = E.execute Numeric.scalar Numeric.hivm 3 2
   (E.PAtom (0,None,E.AAlloc (E.ASDefault,[2],E.Float32Type),E.PDone)) [] E.empty_memory in
 assert (status = E.SemanticError E.StaticProgramError);
 assert (after = (!state).memory && after.memory_next_allocation = 1);
 print_endline "CTree: post-commit SSA arity error matches legacy memory PASS"

let () =
 (* Independent state-transformer reference: compare every budget, not just
    successful executions. Includes nested scope and loop overflow/errors. *)
 let z = Numeric.z_of_int in
 let int n = E.SVInt (E.IndexType,z n) in
 let atom op next = E.PAtom (7,Some 9,op,next) in
 let alloc = E.AAlloc (E.ASDefault,[2],E.Float32Type) in
 let body = E.PIf (8,3,atom alloc E.PDone,E.PDone,E.PDone) in
 let programs = [E.PDone;atom alloc (atom alloc E.PDone);
   E.PAtom (7,None,alloc,E.PDone);
   E.PAtom (7,None,E.AUnsupported,E.PDone);
   E.PIf (8,0,body,atom alloc E.PDone,body);
   E.PFor (6,3,0,1,2,body,body);
   E.PFor (6,3,0,1,2,E.PFor (5,4,0,1,2,body,E.PDone),body);
   E.PFor (6,3,0,1,2,E.PAtom (7,None,E.AUnsupported,E.PDone),body)] in
 let envs = [List.mapi (fun n v -> n,int v) [0;0;1];
   List.mapi (fun n v -> n,int v) [0;3;1];
   List.mapi (fun n v -> n,int v) [1;3;0];
   [0,E.SVInt(E.IntegerType(8,E.Signless),z 126);
    1,E.SVInt(E.IntegerType(8,E.Signless),z 127);
    2,E.SVInt(E.IntegerType(8,E.Signless),z 2)]; []] in
 let checked = ref 0 in
 List.iter (fun p -> List.iter (fun env ->
  List.iter (fun mf -> for fuel = 0 to 80 do
   let tree = E.execute_budget Numeric.scalar Numeric.hivm fuel mf p env E.empty_memory in
   let reference = E.reference_execute Numeric.scalar Numeric.hivm fuel mf p env E.empty_memory in
   assert (tree = reference); incr checked
  done) [0;1;2;8]) envs) programs;
 Printf.printf "CTree: %d exact reference comparisons (status/state/log/remaining budget) PASS\n%!" !checked
