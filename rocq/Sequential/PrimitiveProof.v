From Stdlib Require Import List.
From CTree Require Import CTree.
From UnifiedInterpreter.Base Require Import Result.
From UnifiedInterpreter.Memory Require Import Model Handler.
From UnifiedInterpreter.Sequential Require Import
  Memory MemoryProof Operations Denotation Reference.

(* Transaction execution agrees with the independent Free-memory reference,
   including rollback, errors and the remaining execution budget. *)
Lemma run_transaction_reference : forall S A f mf (p : cm S A) m log,
  run_tree_budget f mf (transaction p) m log =
  ref_transaction mf p f m log.
Proof.
  intros S A f mf p m log.
  destruct f as [|f]; [reflexivity|].
  cbn [run_tree_budget transaction CTree.trigger observe handle_seq ref_transaction].
  unfold transaction, CTree.trigger. cbn.
  rewrite embed_preserves_memory.
  destruct (handle_memory mf p m) as [[[r m'] events]|err]; [|reflexivity].
  destruct r; [|reflexivity].
  destruct f; reflexivity.
Qed.
