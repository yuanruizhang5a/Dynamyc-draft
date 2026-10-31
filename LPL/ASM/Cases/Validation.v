(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** Negative syntax checks, dead ends, failed observations and stutters. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL Require Import Signature Rules.
From CyclistRocq.LPL.ASM Require Import Syntax.
From CyclistRocq.LPL.ASM Require Import Support.
Import ListNotations.
Definition unit_eq_dec : forall x y : unit, {x=y}+{x<>y}.
Proof. decide equality. Defined.
Definition singleton_machine (d : state_description) (code : list (transition unit)) : ASM.
Proof.
  refine (Machine unit (fun x y => unit_eq_dec x y) [tt] _ _ (fun _ => d) code tt).
  - intros []; cbn; auto.
  - repeat constructor; cbn; auto.
Defined.
Definition empty_description := StateDescription [].
Definition stopped := singleton_machine empty_description [].

Definition invalid_term := singleton_machine empty_description
  [unconditional tt tt (vname 0) (Fun 2 [])].

Definition impure_description := singleton_machine (StateDescription [First Truth]) [].

Definition contradictory := singleton_machine (StateDescription [Falsity]) [].

Definition disconnected : ASM.
Proof.
  refine (Machine bool Bool.bool_dec [false;true] _ _ (fun _ => empty_description) [] false).
  - intros []; cbn; auto.
  - repeat constructor; cbn; intuition discriminate.
Defined.
Module TypedModel.
  Module S <: SIGNATURE.
    Definition sort := bool.
    Definition sort_eq_dec := Bool.bool_dec.
    Definition function_symbol := unit.
    Definition predicate_symbol := unit.
    Definition function_eq_dec := unit_eq_dec.
    Definition predicate_eq_dec := unit_eq_dec.
    Definition function_arguments (_ : function_symbol) : list sort := [].
    Definition function_result (_ : function_symbol) : sort := true.
    Definition predicate_arguments (_ : predicate_symbol) : list sort := [].
    Definition function_arity f := length (function_arguments f).
    Definition predicate_arity p := length (predicate_arguments p).
  End S.
  Module Kernel.
    Module Core := MakeRules S.
    Module Model <: Core.Pr.Sem.INTERPRETATION.
      Definition interpretation := Core.Pr.Sem.Model (fun _ => unit) (fun _ => tt)
        (fun _ _ => tt) (fun _ _ => True).
    End Model.
    Include Core.ForModel Model.
  End Kernel.
  Module A := MakeASM S Kernel.
  Definition machine (assertion_sort : bool) (bad_assignment : bool) : A.ASM.
  Proof.
    refine (A.Machine unit unit_eq_dec [tt] _ _
      (fun _ => A.StateDescription [A.Syn.Equal (A.Syn.Var (assertion_sort,0%nat)) (A.Syn.Fun tt [])])
      (if bad_assignment then [A.unconditional tt tt (false,0%nat) (A.Syn.Fun tt [])] else []) tt).
    - intros []; cbn; auto.
    - repeat constructor; cbn; auto.
  Defined.
End TypedModel.
