From Stdlib Require Import List Arith Lia.
From CTree Require Import CTree.
From UnifiedInterpreter.Base Require Import Result.
From UnifiedInterpreter.Memory Require Import Model.
From UnifiedInterpreter.Sequential Require Import Memory Denotation.

(* Observing a tree never increases the caller's remaining execution budget. *)
Lemma run_tree_budget_remaining_le : forall S A fuel mf (t : tree S A) m log,
  snd (run_tree_budget fuel mf t m log) <= fuel.
Proof.
  intros S A fuel.
  induction fuel as [|fuel IH]; intros mf t m log.
  - cbn. reflexivity.
  - cbn [run_tree_budget]. destruct (observe t).
    + destruct r; cbn; lia.
    + cbn; lia.
    + eapply Nat.le_trans; [apply IH | lia].
    + eapply Nat.le_trans; [apply IH | lia].
    + destruct (handle_seq mf e m) as [[[x m'] events]|err].
      * eapply Nat.le_trans; [apply IH | lia].
      * cbn; lia.
    + destruct c.
Qed.
