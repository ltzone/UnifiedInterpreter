From Stdlib Require Import List ZArith Bool.
From UnifiedInterpreter.Base Require Import Result Free.
From UnifiedInterpreter.Type Require Import MLIR HFusion.
From UnifiedInterpreter.Tensor Require Import Model.
From UnifiedInterpreter.Value Require Import Scalar.
From UnifiedInterpreter.Memory Require Import Model Effects.
From UnifiedInterpreter.Unified Require Import Errors.
From UnifiedInterpreter.HFusion Require Import Instr Runtime.
From UnifiedInterpreter.HFusion.Semantics Require Import Memory Structured ElemwiseBinary Common.
From UnifiedInterpreter.HIVM Require Import Instr Numeric Arith Value Execution Semantics.
From UnifiedInterpreter.Sequential Require Import Syntax.
Import ListNotations.
Set Implicit Arguments.
Open Scope Z_scope.

Fixpoint lookup {S} (name : nat) (env : seq_env S) : result runtime_error (seq_value S) :=
 match env with [] => Error StaticProgramError
 | (key,v)::rest => if Nat.eqb name key then Ok v else lookup name rest end.
Definition as_int {S} (v : seq_value S) : result runtime_error (mlir_type * Z) :=
 match v with SVInt ty z => Ok (ty,z) | _ => Error StaticProgramError end.
Definition as_memref {S} (v : seq_value S)
 : result runtime_error (descriptor_id * list nat * mlir_type) :=
 match v with SVMemref id sh ty => Ok (id,sh,ty) | _ => Error StaticProgramError end.
Definition index_value {S} (env : seq_env S) (i : index_term) : result runtime_error Z :=
 match i with Literal z => Ok z | SSAIndex n =>
 v <-? lookup n env ;; p <-? as_int v ;; Ok (snd p) end.
Fixpoint indices {S} (env : seq_env S) (positive : bool) (is : list index_term)
 : result runtime_error (list nat) :=
 match is with [] => Ok [] | i::rest =>
 z <-? index_value env i ;;
 if (z <? 0) || (positive && Z.eqb z 0) then Error InvalidShape else
 ns <-? indices env positive rest ;; Ok (Z.to_nat z::ns) end.
Fixpoint declared_shape (declared : list Z) (actual : list nat) : bool :=
 match declared,actual with
 | [],[] => true
 | d::ds,n::ns => (Z.eqb d (-1) || Z.eqb d (Z.of_nat n)) && declared_shape ds ns
 | _,_ => false end.
Definition cm S A := memory_computation S (result runtime_error A).
Definition lift {S A} (x : result runtime_error A) : cm S A := Return x.
Definition mbind {S A B} (p : cm S A) (k : A -> cm S B) : cm S B :=
 Free.bind p (fun r => match r with Ok v => k v | Error e => Return (Error e) end).
Definition raw {S A} (p : memory_computation S A) : cm S A :=
 Free.bind p (fun v => Return (Ok v)).
Notation "x <-m p ;; k" := (mbind p (fun x => k))
 (at level 100, p at next level, right associativity).
Definition read_tensor {S} (v : seq_value S) : cm S (value S) :=
 match v with SVTensor t => lift (Ok t) | SVView v => materialize v
 | _ => lift (Error StaticProgramError) end.
Definition destination {S} (fresh : bool) (v : seq_value S) : cm S (value S) :=
 match v with SVMemref _ sh ty =>
 if fresh then lift (Ok (EmptyTensor sh ty)) else lift (Error StaticProgramError)
 | _ => read_tensor v end.
Definition deliver {S} (dst : seq_value S) (v : value S) : cm S (option (seq_value S)) :=
 match dst with
 | SVMemref id _ _ => _ <-m write_result v id ;; lift (Ok None)
 | _ => lift (Ok (Some (SVTensor v))) end.
Definition elementwise {S} (dst : value S) (v : seq_value S)
 : cm S (elementwise_operand S (shape dst)) :=
 match v with
 | SVFloat ty x => lift (Ok (ElementwiseScalar ty x))
 | _ => t <-m read_tensor v ;;
   match t with
   | EmptyTensor _ _ => lift (Error ReadUninitialized)
   | DefinedTensor (PackTensor sh ty xs) =>
     match list_eq_dec Nat.eq_dec sh (shape dst) with
     | left H => lift (Ok (ElementwiseTensor (eq_rect sh (fun sh => tensor S sh ty) xs _ H)))
     | right _ => lift (Error InvalidShape)
     end
   end
 end.
Definition seq_operand {S} (v : seq_value S) : cm S (operand S) :=
 match v with SVFloat ty x => lift (Ok (ScalarOperand ty x))
 | _ => t <-m read_tensor v ;; lift (Ok (TensorOperand t)) end.

Definition eval_atom {S} `{ScalarOps S} `{Numeric S}
 (env : seq_env S) (op : atom) : cm S (option (seq_value S)) :=
 let get n := lift (lookup n env) in
 let int n := v <-m get n ;; lift (as_int v) in
 let mem n := v <-m get n ;; lift (as_memref v) in
 let some v := lift (Ok (Some v)) in
 match op with
 | AInt ty z => z <-m lift (sem_integer_constant ty z) ;; some (SVInt ty z)
 | AFloat ty l => x <-m lift (sem_float_constant ty l) ;; some (SVFloat ty x)
 | AInteger oper ty a b =>
   x <-m int a ;; y <-m int b ;;
   if mlir_element_type_eqb (fst x) ty && mlir_element_type_eqb (fst y) ty then
   z <-m lift (sem_integer_binary oper ty (snd x) (snd y)) ;; some (SVInt ty z)
   else lift (Error StaticProgramError)
 | ACompare pred a b => x <-m int a ;; y <-m int b ;;
   if mlir_element_type_eqb (fst x) (fst y) then
   z <-m lift (sem_integer_compare pred (fst x) (snd x) (snd y)) ;;
   some (SVInt (IntegerType 1 Signless) z) else lift (Error StaticProgramError)
 | ACast oper ty a => x <-m int a ;;
   z <-m lift (sem_integer_cast oper (fst x) ty (snd x)) ;; some (SVInt ty z)
 | AEmpty sh ty => t <-m lift (sem_empty sh ty) ;; some (SVTensor t)
 | AAlloc space sh ty => id <-m raw (sem_memref_alloc space ty sh) ;; some (SVMemref id sh ty)
 | AReinterpret a off sh strides => p <-m mem a ;; z <-m lift (index_value env off) ;;
   let '(id,_,ty) := p in
   id <-m raw (sem_memref_reinterpret_cast id z sh strides) ;; some (SVMemref id sh ty)
 | ASubview a os sz st decl => p <-m mem a ;;
   os <-m lift (indices env false os) ;; sz <-m lift (indices env false sz) ;;
   st <-m lift (indices env true st) ;;
   if declared_shape decl sz then let '(id,_,ty) := p in
   id <-m raw (sem_memref_subview id os sz st) ;; some (SVMemref id sz ty)
   else lift (Error InvalidShape)
 | ASlice a os sz st decl => v <-m get a ;; t <-m read_tensor v ;;
   os <-m lift (indices env false os) ;; sz <-m lift (indices env false sz) ;;
   st <-m lift (indices env true st) ;;
   if declared_shape decl sz then
   t <-m lift (sem_extract_slice t os sz st) ;; some (SVTensor t)
   else lift (Error InvalidShape)
 | AToTensor a access => p <-m mem a ;; let '(id,sh,ty) := p in
   v <-m raw (sem_bufferization_to_tensor id sh ty access) ;; some (SVView v)
 | ACopy a b => p <-m mem a ;; q <-m mem b ;;
   let '(a,sh,ty) := p in let '(b,sh',ty') := q in
   if shape_eq sh sh' && mlir_element_type_eqb ty ty' then
   _ <-m raw (sem_memref_copy sh a b) ;; lift (Ok None)
   else lift (Error InvalidShape)
 | AStore a b writable => v <-m get a ;; t <-m read_tensor v ;; p <-m mem b ;;
   if writable then let '(id,_,_) := p in
   _ <-m write_result t id ;; lift (Ok None) else lift (Error StaticProgramError)
 | AFill hivm a dst => x <-m get a ;; d <-m get dst ;; t <-m destination true d ;;
   match x with SVFloat ty x =>
    v <-m lift (if hivm then evaluate (BroadcastRequest (ScalarOperand ty x) t [])
      else sem_linalg_fill ty x t) ;; deliver d v
   | _ => lift (Error StaticProgramError) end
 | AAdd hivm a b dst => a <-m get a ;; b <-m get b ;; d <-m get dst ;;
   t <-m destination false d ;;
   v <-m (if hivm then
     a <-m seq_operand a ;; b <-m seq_operand b ;;
     lift (evaluate (BinaryRequest VAdd a b t))
    else a <-m elementwise t a ;; b <-m elementwise t b ;;
     xs <-m lift (sem_linalg_elemwise_binary LinalgAdd LinalgCastSigned (element_type t) a b) ;;
     lift (Ok (DefinedTensor (PackTensor (shape t) (element_type t) xs)))) ;;
   deliver d v
 | AUnsupported => lift (Error UnsupportedInstruction)
 end.
