From Stdlib Require Import List.
From UnifiedInterpreter.Sequential Require Import Syntax Operations Denotation MemoryProof.
From UnifiedInterpreter.Memory Require Import Model Handler.
From UnifiedInterpreter.Value Require Import Scalar.
From UnifiedInterpreter.HIVM Require Import Numeric.
From UnifiedInterpreter.Base Require Import Result.
Import ListNotations.

(* Every atomic operation's successful Free memory interpretation transports
   to the program interpreter, with the returned SSA value and memory committed.
   Memory diagnostic events do not become program control-flow responses. *)
Lemma atom_success_correspondence {S} `{ScalarOps S} `{Numeric S}
    op (env : seq_env S) m loc name memory_fuel v m' events env' :
  handle_memory memory_fuel (eval_atom env op) m = Ok (Ok v,m',events) ->
  bind_result name v env = Ok env' ->
  execute 3 memory_fuel (PAtom loc name op PDone) env m =
    (Finished env',m',[loc]).
Proof.
  intros Hmemory Hbind.
  unfold execute, run_tree. cbn.
  rewrite embed_preserves_memory, Hmemory. cbn.
  change (fst (run_tree_budget 1 memory_fuel
    (tbind (pure (bind_result name v env)) (fun e => ret e)) m' [loc]) =
    (Finished env',m',[loc])).
  rewrite Hbind. reflexivity.
Qed.

(* An unsuccessful atomic transaction preserves its input memory even when
   the Free computation produced an intermediate state before an inner error.
   error_status also classifies Unsupported and budget exhaustion distinctly. *)
Lemma atom_failure_rollback {S} `{ScalarOps S} `{Numeric S}
    op (env : seq_env S) m loc name memory_fuel err :
  (handle_memory memory_fuel (eval_atom env op) m = Error err \/
   exists m' events,
     handle_memory memory_fuel (eval_atom env op) m = Ok (Error err,m',events)) ->
  execute 3 memory_fuel (PAtom loc name op PDone) env m =
    (error_status err,m,[loc]).
Proof.
  intros Hfailure. unfold execute, run_tree. cbn.
  rewrite embed_preserves_memory.
  destruct Hfailure as [Houter | [m' [events Hinner]]].
  - rewrite Houter. reflexivity.
  - rewrite Hinner. reflexivity.
Qed.

(* SSA result-arity failure occurs after a successful transaction has committed;
   it does not roll back that transaction's memory. *)
Lemma atom_binding_failure_commits {S} `{ScalarOps S} `{Numeric S}
    op (env : seq_env S) m loc name memory_fuel v m' events err :
  handle_memory memory_fuel (eval_atom env op) m = Ok (Ok v,m',events) ->
  bind_result name v env = Error err ->
  execute 3 memory_fuel (PAtom loc name op PDone) env m =
    (error_status err,m',[loc]).
Proof.
  intros Hmemory Hbind.
  unfold execute, run_tree. cbn.
  rewrite embed_preserves_memory, Hmemory. cbn.
  change (fst (run_tree_budget 1 memory_fuel
    (tbind (pure (bind_result name v env)) (fun e => ret e)) m' [loc]) =
    (error_status err,m',[loc])).
  rewrite Hbind. reflexivity.
Qed.
