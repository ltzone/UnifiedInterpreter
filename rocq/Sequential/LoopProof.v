From Stdlib Require Import List ZArith Lia.
From CTree Require Import CTree.
From UnifiedInterpreter.Sequential Require Import Syntax Operations Denotation Reference RunFacts FuelFacts BindAssoc.
From UnifiedInterpreter.Memory Require Import Model.
From UnifiedInterpreter.Base Require Import Result.
Import ListNotations.
Lemma run_loop_reference : forall S loc iv ty start stop stride
    (body : seq_env S -> tree S (seq_env S)) env fuel mf limit m log,
  (fuel <= limit)%nat ->
  run_tree_budget fuel mf (loop loc iv ty start stop stride body env) m log =
  ref_loop_bounded limit loc iv ty stop stride
    (fun e f m l => run_tree_budget f mf (body e) m l) env start fuel m log.
Proof.
intros S loc iv ty start stop stride body env fuel. revert start.
induction fuel as [fuel IH] using lt_wf_ind.
intros start mf limit m log Hlimit. destruct fuel as [|fuel].
- destruct limit; reflexivity.
- destruct limit as [|limit]; [lia|].
  change (run_tree_budget (Datatypes.S fuel) mf
    (CTree.bind
      (if start <? stop then
        CTree.bind (mark loc (body ((iv,SVInt ty start)::env)))
          (fun r => match r with
           | Error e => Ret (inr (Error e))
           | Ok _ => match Arith.sem_integer_binary Instr.ArithAddI ty start stride with
             | Error e => Ret (inr (Error e))
             | Ok next => if start <? next then Ret (inl next)
               else Ret (inr (Error Errors.NumericFailure))
             end end)
       else Ret (inr (Ok tt)))
      (fun lr => match lr with
       | inl next => Guard (loop loc iv ty next stop stride body env)
       | inr r => Ret r end)) m log =
    ref_loop_bounded (Datatypes.S limit) loc iv ty stop stride
      (fun e f m l => run_tree_budget f mf (body e) m l)
      env start (Datatypes.S fuel) m log).
  destruct (start <? stop) eqn:Hstop.
  2: { cbn [run_tree_budget ref_loop_bounded]. rewrite Hstop. reflexivity. }
  rewrite run_bind_assoc.
  transitivity (run_tree_budget (Datatypes.S fuel) mf
    (tbind (mark loc (body ((iv,SVInt ty start)::env)))
      (fun _ => match Arith.sem_integer_binary Instr.ArithAddI ty start stride with
       | Error e => fail e
       | Ok next => if start <? next
         then Guard (loop loc iv ty next stop stride body env)
         else fail Errors.NumericFailure end)) m log).
  2: {
    rewrite run_tbind_reference. unfold ref_bind.
    cbn [run_tree_budget mark]. cbn [ref_loop_bounded]. rewrite Hstop.
    unfold mark. cbn.
    assert (Hret :
      run_tree_budget fuel mf
        (CTree.subst (fun _ : unit => body ((iv,SVInt ty start)::env)) (Ret tt))
        m (loc::log) =
      run_tree_budget fuel mf (body ((iv,SVInt ty start)::env)) m (loc::log))
      by (destruct fuel; reflexivity).
    rewrite Hret.
    pose proof (run_tree_budget_remaining_le S (seq_env S) fuel mf
      (body ((iv,SVInt ty start)::env)) m (loc::log)) as Hremaining.
    destruct (run_tree_budget fuel mf (body ((iv,SVInt ty start)::env))
      m (loc::log)) as [[[status m'] events] remaining] eqn:Hbody.
    cbn in Hremaining. destruct status; try reflexivity.
    destruct (Arith.sem_integer_binary Instr.ArithAddI ty start stride)
      as [next|err]; cbn.
    - destruct (start <? next); cbn.
      + apply IH; lia.
      + rewrite rev_involutive. reflexivity.
    - rewrite rev_involutive. reflexivity.
  }
  unfold tbind. apply run_bind_congr.
  intros [x|err] f mem logs.
  + destruct (Arith.sem_integer_binary Instr.ArithAddI ty start stride)
      as [next|err]; [destruct (start <? next)|]; destruct f; reflexivity.
  + destruct f; reflexivity.
Qed.
