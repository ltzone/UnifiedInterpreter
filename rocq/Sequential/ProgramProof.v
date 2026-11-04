From Stdlib Require Import List PeanoNat.
From UnifiedInterpreter.Sequential Require Import Syntax Operations Denotation.
From UnifiedInterpreter.Memory Require Import Model.
From UnifiedInterpreter.Value Require Import Scalar.
From UnifiedInterpreter.HIVM Require Import Numeric.
From UnifiedInterpreter.Base Require Import Result.
Import ListNotations.

(* The actual allocation response becomes an SSA descriptor binding;
   lookup at every other name retains its previous result. *)
Lemma allocate_binds_ssa {S} `{ScalarOps S} `{Numeric S}
    loc name space sh ty (env : seq_env S) m id m' :
  allocate_memref space ty sh m = (id,m') ->
  execute 3 2 (PAtom loc (Some name) (AAlloc space sh ty) PDone) env m =
    (Finished ((name,SVMemref id sh ty)::env),m',[loc]) /\
  lookup name ((name,SVMemref id sh ty)::env) = Ok (SVMemref id sh ty) /\
  (forall key, key <> name ->
    lookup key ((name,SVMemref id sh ty)::env) = lookup key env).
Proof.
  intros Halloc. split.
  - unfold execute. cbn. cbn in Halloc. inversion Halloc. reflexivity.
  - split.
    + cbn. now rewrite Nat.eqb_refl.
    + intros key Hneq. cbn. apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.
