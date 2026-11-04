From Stdlib Require Import List ZArith Bool.
From CTree Require Import CTree.
From UnifiedInterpreter.Sequential Require Import
  Syntax Operations Denotation Reference RunFacts PrimitiveProof LoopProof.
From UnifiedInterpreter.Memory Require Import Model.
From UnifiedInterpreter.Value Require Import Scalar.
From UnifiedInterpreter.HIVM Require Import Numeric.
From UnifiedInterpreter.Type Require Import MLIR.
From UnifiedInterpreter.Base Require Import Result.
From UnifiedInterpreter.Unified Require Import Errors.

Lemma ref_bind_ext : forall S A B (p q : ref_comp S A)
  (k h : A -> ref_comp S B),
  (forall f m l, p f m l = q f m l) ->
  (forall x f m l, k x f m l = h x f m l) ->
  forall f m l, ref_bind p k f m l = ref_bind q h f m l.
Proof.
  intros S A B p q k h Hp Hk f m l.
  unfold ref_bind. rewrite Hp.
  destruct (q f m l) as [[[status m'] events] remaining].
  destruct status; auto.
Qed.

Lemma run_pure_reference : forall S A f mf (r : result runtime_error A)
  (m : memory_state S) log,
  run_tree_budget f mf (pure r) m log = ref_pure r f m log.
Proof.
  intros. destruct f; [reflexivity|]. destruct r; reflexivity.
Qed.

Lemma run_mark_reference : forall S A f mf loc (t : tree S A) m log,
  run_tree_budget f mf (mark loc t) m log =
  ref_mark loc (fun f m l => run_tree_budget f mf t m l) f m log.
Proof.
  intros. destruct f; [reflexivity|]. unfold mark.
  cbn [run_tree_budget]. rewrite observe_bind_exact.
  unfold CTree.trigger. cbn.
  destruct f as [|f]; [reflexivity|].
  cbn [run_tree_budget]. rewrite observe_bind_exact. reflexivity.
Qed.

Lemma ref_loop_bounded_ext : forall S limit loc iv ty stop stride
  (b c : seq_env S -> ref_comp S (seq_env S)),
  (forall env f m log, b env f m log = c env f m log) ->
  forall env i fuel m log,
  ref_loop_bounded limit loc iv ty stop stride b env i fuel m log =
  ref_loop_bounded limit loc iv ty stop stride c env i fuel m log.
Proof.
  intros S limit. induction limit as [|limit IH];
    intros loc iv ty stop stride b c Hb env i fuel m log; [reflexivity|].
  destruct fuel as [|fuel]; [reflexivity|].
  cbn [ref_loop_bounded]. destruct (Z.ltb i stop); [|reflexivity].
  rewrite Hb.
  destruct (c ((iv,SVInt ty i)::env) fuel m (loc::log))
    as [[[status m'] events] remaining].
  destruct status; try reflexivity.
  destruct (Arith.sem_integer_binary Instr.ArithAddI ty i stride)
    as [next|e]; [|reflexivity].
  destruct (Z.ltb i next); [apply IH; exact Hb|reflexivity].
Qed.

(* Exact agreement for every program and budget, including nested regions and
   loops, memory commits, failures, logs and remaining execution budget. *)
Theorem program_conservativity : forall S `{ScalarOps S} `{Numeric S}
  mf p env fuel m log,
  run_tree_budget fuel mf (denote p env) m log =
  reference mf p env fuel m log.
Proof.
  intros S H H0 mf p.
  induction p; intros env fuel m log; cbn [denote reference].
  - apply run_pure_reference.
  - rewrite run_mark_reference. destruct fuel; [reflexivity|].
    cbn [ref_mark]. rewrite run_tbind_reference. apply ref_bind_ext.
    + intros. apply run_transaction_reference.
    + intros. rewrite run_tbind_reference. apply ref_bind_ext.
      * intros. apply run_pure_reference.
      * intros. apply IHp.
  - rewrite run_mark_reference. destruct fuel; [reflexivity|].
    cbn [ref_mark]. rewrite run_tbind_reference. apply ref_bind_ext.
    + intros. apply run_pure_reference.
    + intros. rewrite run_tbind_reference. apply ref_bind_ext.
      * intros. apply run_pure_reference.
      * intros. rewrite run_tbind_reference. apply ref_bind_ext.
        -- intros. destruct (Z.eqb (snd x0) 0); [apply IHp2 | apply IHp1].
        -- intros. apply IHp3.
  - rewrite run_mark_reference. destruct fuel; [reflexivity|].
    cbn [ref_mark].
    repeat (rewrite run_tbind_reference; apply ref_bind_ext;
      [intros; apply run_pure_reference | intros]).
    destruct (mlir_element_type_eqb (fst x2) (fst x3) &&
      mlir_element_type_eqb (fst x2) (fst x4) && (0 <? snd x4))%bool.
    + rewrite run_tbind_reference. apply ref_bind_ext.
      * intros. unfold ref_loop.
        rewrite (run_loop_reference _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _)).
        apply ref_loop_bounded_ext. intros. apply IHp1.
      * intros. apply IHp2.
    + apply run_pure_reference.
Qed.

Corollary execute_conservativity : forall S `{ScalarOps S} `{Numeric S}
  fuel mf p env m,
  execute_budget fuel mf p env m = reference_execute fuel mf p env m.
Proof.
  intros. apply program_conservativity.
Qed.
