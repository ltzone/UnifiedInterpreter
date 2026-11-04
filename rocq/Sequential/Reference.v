(* Direct sequential state-transformer semantics. No CTree operations or runner
   calls occur here. Primitive atoms and the original finite Free handler are
   shared; program control and loop execution are defined independently. *)
From Stdlib Require Import List ZArith Bool.
From UnifiedInterpreter.Sequential Require Import Syntax Operations Denotation.
From UnifiedInterpreter.Memory Require Import Model Handler.
From UnifiedInterpreter.Value Require Import Scalar.
From UnifiedInterpreter.HIVM Require Import Numeric Arith.
From UnifiedInterpreter.HFusion Require Import Instr.
From UnifiedInterpreter.Type Require Import MLIR.
From UnifiedInterpreter.Base Require Import Result.
From UnifiedInterpreter.Unified Require Import Errors.
Import ListNotations.
Set Implicit Arguments.
Open Scope Z_scope.

Definition ref_out S A := ((execution_status A * memory_state S * list nat) * nat)%type.
Definition ref_comp S A := nat -> memory_state S -> list nat -> ref_out S A.
Definition ref_exhausted {S A} (m : memory_state S) log : ref_out S A :=
 ((BudgetExhausted,m,rev log),0%nat).
Definition ref_pure {S A} (r : result runtime_error A) : ref_comp S A :=
 fun fuel m log => match fuel with
 | O => ref_exhausted m log
 | S f => ((match r with Ok x => Finished x | Error e => error_status e end,m,rev log),f)
 end.
Definition ref_bind {S A B} (p : ref_comp S A) (k : A -> ref_comp S B) : ref_comp S B :=
 fun fuel m log =>
 let '((status,m',events),remaining) := p fuel m log in
 match status with
 | Finished x => k x (Datatypes.S remaining) m' (rev events)
 | SemanticError e => ((SemanticError e,m',events),remaining)
 | Unsupported => ((Unsupported,m',events),remaining)
 | BudgetExhausted => ((BudgetExhausted,m',events),remaining)
 | Deadlock => ((Deadlock,m',events),remaining)
 end.
Definition ref_mark {S A} loc (p : ref_comp S A) : ref_comp S A :=
 fun fuel m log => match fuel with
 | O => ref_exhausted m log | S f => p f m (loc::log) end.
Definition ref_transaction {S A} memory_fuel (p : cm S A) : ref_comp S A :=
 fun fuel m log => match fuel with
 | O => ref_exhausted m log
 | S f => match handle_memory memory_fuel p m with
   | Error e => ((error_status e,m,rev log),f)
   | Ok (Error e,_,_) => ((error_status e,m,rev log),f)
   | Ok (Ok x,m',_) => ref_pure (Ok x) f m' log
   end
 end.

(* [limit] only makes the independent loop evaluator structurally recursive.
   Its public caller supplies [limit = fuel]; the conservativity proof shows
   that this extra bound never truncates execution before the tree budget. *)
Fixpoint ref_loop_bounded {S} (limit : nat) loc iv ty stop stride
 (body : seq_env S -> ref_comp S (seq_env S)) (env : seq_env S)
 (i : Z) : ref_comp S unit :=
 fun fuel m log => match limit with
 | O => ref_exhausted m log
 | S limit' => match fuel with
   | O => ref_exhausted m log
   | S f => if i <? stop then
     let '((status,m',events),remaining) := body ((iv,SVInt ty i)::env) f m (loc::log) in
     match status with
     | Finished _ => match sem_integer_binary ArithAddI ty i stride with
       | Error e => ((error_status e,m',events),remaining)
       | Ok next => if i <? next then
          ref_loop_bounded limit' loc iv ty stop stride body env next remaining m' (rev events)
          else ((error_status NumericFailure,m',events),remaining)
       end
     | SemanticError e => ((SemanticError e,m',events),remaining)
     | Unsupported => ((Unsupported,m',events),remaining)
     | BudgetExhausted => ((BudgetExhausted,m',events),remaining)
     | Deadlock => ((Deadlock,m',events),remaining)
     end
     else ((Finished tt,m,rev log),f)
   end
 end.
Definition ref_loop {S} loc iv ty start stop stride body (env : seq_env S)
 : ref_comp S unit := fun fuel =>
 ref_loop_bounded fuel loc iv ty stop stride body env start fuel.

Fixpoint reference {S} `{ScalarOps S} `{Numeric S} memory_fuel
 (p : program) (env : seq_env S) : ref_comp S (seq_env S) :=
 match p with
 | PDone => ref_pure (Ok env)
 | PAtom loc name op next => ref_mark loc
   (ref_bind (ref_transaction memory_fuel (eval_atom env op)) (fun v =>
    ref_bind (ref_pure (bind_result name v env)) (reference memory_fuel next)))
 | PIf loc cond yes no next => ref_mark loc
   (ref_bind (ref_pure (lookup cond env)) (fun v =>
    ref_bind (ref_pure (as_int v)) (fun c =>
    ref_bind (reference memory_fuel (if Z.eqb (snd c) 0 then no else yes) env)
      (fun _ => reference memory_fuel next env))))
 | PFor loc iv lo hi st body next => ref_mark loc
   (ref_bind (ref_pure (lookup lo env)) (fun l =>
    ref_bind (ref_pure (lookup hi env)) (fun h =>
    ref_bind (ref_pure (lookup st env)) (fun s =>
    ref_bind (ref_pure (as_int l)) (fun l =>
    ref_bind (ref_pure (as_int h)) (fun h =>
    ref_bind (ref_pure (as_int s)) (fun s =>
     if mlir_element_type_eqb (fst l) (fst h) && mlir_element_type_eqb (fst l) (fst s)
        && (0 <? snd s) then
     ref_bind (ref_loop loc iv (fst l) (snd l) (snd h) (snd s)
       (reference memory_fuel body) env) (fun _ => reference memory_fuel next env)
     else ref_pure (Error StaticProgramError))))))))
 end.
Definition reference_execute {S} `{ScalarOps S} `{Numeric S}
 fuel memory_fuel p env m := reference memory_fuel p env fuel m [].
