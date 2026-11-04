From CTree Require Import CTree.
From UnifiedInterpreter.Sequential Require Import Memory Denotation RunFacts.

(* Reassociation preserves exact execution, including remaining budget. *)
Lemma run_bind_assoc : forall S A B C fuel mf
    (t : ctree (seq_effect S) no_choice A)
    (k : A -> ctree (seq_effect S) no_choice B)
    (h : B -> tree S C) m log,
  run_tree_budget fuel mf (CTree.bind (CTree.bind t k) h) m log =
  run_tree_budget fuel mf
    (CTree.bind t (fun x => CTree.bind (k x) h)) m log.
Proof.
  intros S A B C fuel mf.
  induction fuel as [|fuel IH]; intros t k h m log.
  - reflexivity.
  - cbn [run_tree_budget]. rewrite !observe_bind_exact.
    destruct (observe t) as [x| |u|u|X e g|X c g] eqn:Ht.
    + rewrite observe_bind_exact. reflexivity.
    + reflexivity.
    + apply IH.
    + apply IH.
    + destruct (handle_seq mf e m) as [[[x m'] events]|err].
      * apply IH.
      * reflexivity.
    + destruct c.
Qed.

(* Pointwise execution equivalence of continuations is preserved by bind. *)
Lemma run_bind_congr : forall S A B mf
    (t : ctree (seq_effect S) no_choice A) (k h : A -> tree S B),
  (forall x fuel m log,
    run_tree_budget fuel mf (k x) m log =
    run_tree_budget fuel mf (h x) m log) ->
  forall fuel m log,
    run_tree_budget fuel mf (CTree.bind t k) m log =
    run_tree_budget fuel mf (CTree.bind t h) m log.
Proof.
  intros S A B mf t k h H. intros fuel. revert t.
  induction fuel as [|fuel IH]; intros t m log.
  - reflexivity.
  - cbn [run_tree_budget]. rewrite !observe_bind_exact.
    destruct (observe t) as [x| |u|u|X e g|X c g] eqn:Ht.
    + exact (H x (Datatypes.S fuel) m log).
    + reflexivity.
    + apply IH.
    + apply IH.
    + destruct (handle_seq mf e m) as [[[x m'] events]|err].
      * apply IH.
      * reflexivity.
    + destruct c.
Qed.
