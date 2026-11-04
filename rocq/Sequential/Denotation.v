From Stdlib Require Import List ZArith Bool.
From CTree Require Import CTree.
From UnifiedInterpreter.Base Require Import Result.
From UnifiedInterpreter.Type Require Import MLIR.
From UnifiedInterpreter.Value Require Import Scalar.
From UnifiedInterpreter.Memory Require Import Model Effects.
From UnifiedInterpreter.Unified Require Import Errors Events.
From UnifiedInterpreter.HFusion Require Import Instr.
From UnifiedInterpreter.HIVM Require Import Numeric Arith.
From UnifiedInterpreter.Sequential Require Import Memory Syntax Operations.
Import ListNotations.
Set Implicit Arguments.
Open Scope Z_scope.

Inductive seq_effect (S : Type) : Type -> Type :=
| MemoryTransaction {A} (p : cm S A) : seq_effect S (result runtime_error A)
| ObserveOperation (location : nat) : seq_effect S unit.
Arguments MemoryTransaction {S A} _.
Arguments ObserveOperation {S} _.
Definition tree S A := ctree (seq_effect S) no_choice (result runtime_error A).
Definition ret {S A} (x : A) : tree S A := Ret (Ok x).
Definition fail {S A} (e : runtime_error) : tree S A := Ret (Error e).
Definition tbind {S A B} (t : tree S A) (k : A -> tree S B) : tree S B :=
 CTree.bind t (fun r => match r with Ok x => k x | Error e => fail e end).
Definition pure {S A} (r : result runtime_error A) : tree S A := Ret r.
Definition transaction {S A} (p : cm S A) : tree S A :=
 CTree.trigger (MemoryTransaction p).
Definition mark {S A} (loc : nat) (t : tree S A) : tree S A :=
 CTree.bind (CTree.trigger (ObserveOperation loc)) (fun _ => t).
Notation "x <-t p ;; k" := (tbind p (fun x => k))
 (at level 100, p at next level, right associativity).
Definition bind_result {S} (name : option nat) (v : option (seq_value S)) (env : seq_env S)
 : result runtime_error (seq_env S) :=
 match name,v with Some n,Some x => Ok ((n,x)::env)
 | None,None => Ok env | _,_ => Error StaticProgramError end.

Definition loop {S} (loc iv : nat) (ty : mlir_type) (start stop stride : Z)
 (body : seq_env S -> tree S (seq_env S)) (env : seq_env S) : tree S unit :=
 CTree.iter (fun i =>
   if i <? stop then
    CTree.bind (mark loc (body ((iv,SVInt ty i)::env))) (fun r =>
     match r with
     | Error e => Ret (inr (Error e))
     | Ok _ => match sem_integer_binary ArithAddI ty i stride with
       | Error e => Ret (inr (Error e))
       | Ok next => if i <? next then Ret (inl next)
          else Ret (inr (Error NumericFailure)) end
     end)
   else Ret (inr (Ok tt))) start.

Fixpoint denote {S} `{ScalarOps S} `{Numeric S} (p : program) (env : seq_env S)
 : tree S (seq_env S) :=
 match p with
 | PDone => ret env
 | PAtom loc name op next => mark loc
   (v <-t transaction (eval_atom env op) ;;
    env' <-t pure (bind_result name v env) ;; denote next env')
 | PIf loc cond yes no next => mark loc
   (v <-t pure (lookup cond env) ;; c <-t pure (as_int v) ;;
    _ <-t (if Z.eqb (snd c) 0 then denote no env else denote yes env) ;;
    denote next env)
 | PFor loc iv lo hi st body next => mark loc
   (l <-t pure (lookup lo env) ;; h <-t pure (lookup hi env) ;; s <-t pure (lookup st env) ;;
    l <-t pure (as_int l) ;; h <-t pure (as_int h) ;; s <-t pure (as_int s) ;;
    if mlir_element_type_eqb (fst l) (fst h) && mlir_element_type_eqb (fst l) (fst s)
       && (0 <? snd s) then
    _ <-t loop loc iv (fst l) (snd l) (snd h) (snd s) (denote body) env ;;
    denote next env
    else fail StaticProgramError)
 end.

Inductive execution_status (A : Type) :=
| Finished (value : A)
| SemanticError (error : runtime_error)
| Unsupported
| BudgetExhausted
| Deadlock.
Arguments Finished {A} _.
Arguments SemanticError {A} _.
Arguments Unsupported {A}.
Arguments BudgetExhausted {A}.
Arguments Deadlock {A}.
Definition error_status {A} (e : runtime_error) : execution_status A :=
 match e with UnsupportedInstruction => Unsupported | OutOfFuel => BudgetExhausted
 | _ => SemanticError e end.

(* Memory transactions commit only on both outer and inner success. Earlier
   successful operations remain committed if a later operation fails. Logs are
   outputs; they are never available to SSA evaluation or numeric operations. *)
Definition handle_seq {S X} (memory_fuel : nat) (e : seq_effect S X) (m : memory_state S)
 : result runtime_error (X * memory_state S * list nat) :=
 match e with
 | ObserveOperation loc => Ok (tt,m,[loc])
 | MemoryTransaction p =>
   match run_memory_tree memory_fuel (embed p) m with
   | Error err => Error err
   | Ok (Error err,_,_) => Error err
   | Ok (Ok v,m',_) => Ok (Ok v,m',[])
   end
 end.
Fixpoint run_tree_budget {S A} (fuel memory_fuel : nat) (t : tree S A)
 (m : memory_state S) (log : list nat)
 : (execution_status A * memory_state S * list nat) * nat :=
 match fuel with O => ((BudgetExhausted,m,rev log),0%nat)
 | S fuel' => match observe t with
   | RetF (Ok v) => ((Finished v,m,rev log),fuel')
   | RetF (Error e) => ((error_status e,m,rev log),fuel')
   | StuckF => ((Deadlock,m,rev log),fuel')
   | GuardF t | StepF t => run_tree_budget fuel' memory_fuel t m log
   | BrF c _ => match c with end
   | VisF e k => match handle_seq memory_fuel e m with
     | Error e => ((error_status e,m,rev log),fuel')
     | Ok (x,m',events) => run_tree_budget fuel' memory_fuel (k x) m' (rev_append events log)
     end
   end
 end.
Definition run_tree {S A} fuel memory_fuel (t : tree S A) m log :=
 fst (run_tree_budget fuel memory_fuel t m log).
Definition execute {S} `{ScalarOps S} `{Numeric S} fuel memory_fuel p env m :=
 run_tree fuel memory_fuel (denote p env) m [].

Definition execute_budget {S} `{ScalarOps S} `{Numeric S} fuel memory_fuel p env m :=
 run_tree_budget fuel memory_fuel (denote p env) m [].
