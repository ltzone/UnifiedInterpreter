From CTree Require Import CTree.

(* Exact one-observation unfolding; no extensionality or bisimulation axiom. *)
Lemma observe_bind_exact {E B A R}
    (t : ctree E B A) (k : A -> ctree E B R) :
  observe (CTree.bind t k) =
  match observe t with
  | RetF x => observe (k x)
  | StuckF => StuckF
  | GuardF u => GuardF (CTree.bind u k)
  | StepF u => StepF (CTree.bind u k)
  | VisF e h => VisF e (fun x => CTree.bind (h x) k)
  | BrF c h => BrF c (fun x => CTree.bind (h x) k)
  end.
Proof.
  unfold CTree.bind, CTree.subst, observe. cbn.
  destruct (_observe t); reflexivity.
Qed.

From Stdlib Require Import List.
From UnifiedInterpreter.Sequential Require Import Syntax Operations Denotation Reference.
From UnifiedInterpreter.Memory Require Import Model.
From UnifiedInterpreter.Base Require Import Result.

Lemma run_tbind_reference : forall S A B fuel mf
    (t : tree S A) (k : A -> tree S B) m log,
  run_tree_budget fuel mf (tbind t k) m log =
  ref_bind (fun f m l => run_tree_budget f mf t m l)
    (fun x f m l => run_tree_budget f mf (k x) m l) fuel m log.
Proof.
  intros S A B fuel mf.
  induction fuel as [|fuel IH]; intros t k m log.
  - reflexivity.
  - unfold tbind at 1. cbn [run_tree_budget].
    rewrite observe_bind_exact.
    destruct (observe t) as [[x|err]| |u|u|X e h|X c h] eqn:Ht.
    + unfold ref_bind. cbn [run_tree_budget]. rewrite Ht. cbn.
      rewrite !rev_involutive. reflexivity.
    + unfold ref_bind. cbn [run_tree_budget]. rewrite Ht. cbn.
      destruct err; reflexivity.
    + unfold ref_bind. cbn [run_tree_budget]. rewrite Ht. reflexivity.
    + fold (tbind u k). rewrite IH. unfold ref_bind.
      cbn [run_tree_budget]. rewrite Ht. reflexivity.
    + fold (tbind u k). rewrite IH. unfold ref_bind.
      cbn [run_tree_budget]. rewrite Ht. reflexivity.
    + unfold ref_bind. cbn [run_tree_budget]. rewrite Ht.
      destruct (handle_seq mf e m) as [[[x m'] events]|err].
      * fold (tbind (h x) k). apply IH.
      * destruct err; reflexivity.
    + destruct c.
Qed.
