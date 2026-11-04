From Stdlib Require Import List ZArith.
From UnifiedInterpreter.Type Require Import MLIR HFusion.
From UnifiedInterpreter.HFusion Require Import Instr Syntax Runtime.
From UnifiedInterpreter.HIVM Require Import Value.
From UnifiedInterpreter.Memory Require Import Model.
Set Implicit Arguments.

Inductive seq_value (S : Type) :=
| SVInt (ty : mlir_type) (z : Z)
| SVFloat (ty : mlir_type) (x : S)
| SVTensor (t : value S)
| SVView (v : runtime_tensor S)
| SVMemref (id : descriptor_id) (sh : list nat) (ty : mlir_type).
Arguments SVInt {S} _ _.
Arguments SVFloat {S} _ _.
Arguments SVTensor {S} _.
Arguments SVView {S} _.
Arguments SVMemref {S} _ _ _.
Definition seq_env S := list (nat * seq_value S).
Inductive index_term := Literal (z : Z) | SSAIndex (name : nat).
Inductive atom :=
| AInt (ty : mlir_type) (z : Z)
| AFloat (ty : mlir_type) (literal : float_literal)
| AInteger (op : arith_binary_operator) (ty : mlir_type) (a b : nat)
| ACompare (predicate a b : nat)
| ACast (op : arith_cast_operator) (ty : mlir_type) (a : nat)
| AEmpty (sh : list nat) (ty : mlir_type)
| AAlloc (space : address_space) (sh : list nat) (ty : mlir_type)
| AReinterpret (a : nat) (offset : index_term) (sh : list nat) (strides : list Z)
| ASubview (a : nat) (offsets sizes strides : list index_term) (declared : list Z)
| ASlice (a : nat) (offsets sizes strides : list index_term) (declared : list Z)
| AToTensor (a : nat) (access : tensor_access)
| ACopy (a b : nat)
| AStore (a b : nat) (writable : bool)
| AFill (hivm : bool) (a dst : nat)
| AAdd (hivm : bool) (a b dst : nat)
| AUnsupported.
Inductive program :=
| PDone
| PAtom (location : nat) (result_name : option nat) (op : atom) (next : program)
| PIf (location condition : nat) (yes no next : program)
| PFor (location iv lo hi step : nat) (body next : program).
