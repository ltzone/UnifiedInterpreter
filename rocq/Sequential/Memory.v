From Stdlib Require Import List.
From CTree Require Import CTree.
From UnifiedInterpreter.Base Require Import Free Result.
From UnifiedInterpreter.Memory Require Import Model Effects Handler.
From UnifiedInterpreter.Unified Require Import Errors Events.
Import ListNotations.
Set Implicit Arguments.

(* The sequential instance has no internal nondeterministic choice. *)
Variant no_choice : Type -> Type := .

Fixpoint embed {V A} (p : memory_computation V A)
    : ctree (memory_effect V) no_choice A :=
  match p with
  | Return x => Ret x
  | Trigger e k => Vis e (fun x => embed (k x))
  end.

Fixpoint run_memory_tree {V A} (fuel : nat)
    (t : ctree (memory_effect V) no_choice A) (m : memory_state V)
    : result runtime_error (A * memory_state V * list event) :=
  match fuel with
  | O => Error OutOfFuel
  | S fuel' =>
    match observe t with
    | RetF x => Ok (x,m,[])
    | StuckF => Error UnsupportedInstruction
    | GuardF t | StepF t => run_memory_tree fuel' t m
    | BrF c _ => match c with end
    | VisF e k =>
      match handle_effect e m with
      | Error e => Error e
      | Ok (x,m',log) =>
        match run_memory_tree fuel' (k x) m' with
        | Error e => Error e
        | Ok (y,m'',log') => Ok (y,m'',log ++ log')
        end
      end
    end
  end.
