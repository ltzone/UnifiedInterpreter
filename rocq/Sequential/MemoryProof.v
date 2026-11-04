From UnifiedInterpreter.Sequential Require Import Memory.
From UnifiedInterpreter.Memory Require Import Effects Model Handler.
From UnifiedInterpreter.Base Require Import Free Result.

(* Embedding preserves the complete observable result, including fuel failure,
   semantic errors, successful memory state, and diagnostic event order. *)
Lemma embed_preserves_memory : forall V A fuel
    (p : memory_computation V A) m,
  run_memory_tree fuel (embed p) m = handle_memory fuel p m.
Proof.
  intros V A fuel.
  induction fuel as [|fuel IH]; intros p m; [reflexivity|].
  destruct p as [x|X e k]; cbn; [reflexivity|].
  destruct (handle_effect e m) as [[[x m'] log]|err]; [|reflexivity].
  rewrite IH. reflexivity.
Qed.
