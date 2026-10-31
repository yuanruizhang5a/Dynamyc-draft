(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * A user-defined heterogeneous theory, including a function-valued heap

    The model supplies all meanings and proves its own store/read law. There
    is no equality decision on heaps and no automatic constructor principle.
    The final generated six-node certificate observes the state after a heap
    assignment, using the unchanged cyclic certification bridge. *)
From Stdlib Require Import List Bool ZArith String.
From CyclistRocq.LPL Require Import Signature Rules RuleGeneration Certification.
Import ListNotations.
Open Scope string_scope.

Module StructureSignature <: SIGNATURE.
  Inductive sort_name := IntSort | BoolSort | HeapSort.
  Definition sort := sort_name.
  Definition sort_eq_dec : forall x y : sort, {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Inductive function_name := Zero | One | TrueValue | Read | Store | Select.
  Definition function_symbol := function_name.
  Inductive predicate_name := Less | Stored.
  Definition predicate_symbol := predicate_name.
  Definition function_eq_dec : forall x y : function_symbol, {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Definition predicate_eq_dec : forall x y : predicate_symbol, {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Definition function_arguments f := match f with
    | Zero | One | TrueValue => [] | Read => [HeapSort;IntSort]
    | Store => [HeapSort;IntSort;IntSort] | Select => [BoolSort;IntSort;IntSort] end.
  Definition function_result f := match f with TrueValue => BoolSort | Store => HeapSort | _ => IntSort end.
  Definition predicate_arguments p := match p with Less => [IntSort;IntSort] | Stored =>
    [HeapSort;IntSort;IntSort] end.
  Definition function_arity f := List.length (function_arguments f).
  Definition predicate_arity p := List.length (predicate_arguments p).
End StructureSignature.
Import StructureSignature.
Definition store (h : Z -> Z) (i v : Z) := fun j => if Z.eq_dec j i then v else h j.
Lemma read_store_same h i v : store h i v i = v.
Proof. unfold store; destruct (Z.eq_dec i i); congruence. Qed.
Lemma read_store_other h i j v : j<>i -> store h i v j = h j.
Proof. intro H; unfold store; destruct (Z.eq_dec j i); congruence. Qed.

Module Kernel.
  Module Core := MakeRules StructureSignature.
  Module Model <: Core.Pr.Sem.INTERPRETATION.
    Module Sem := Core.Pr.Sem.
    Definition Carrier ty : Type := match ty with IntSort => Z | BoolSort => bool | HeapSort => Z -> Z end.
    Definition point ty : Carrier ty := match ty with IntSort => 0%Z | BoolSort => false | HeapSort => fun _
      => 0%Z end.
    Definition fn f : Sem.arguments Carrier (function_arguments f) -> Carrier (function_result f) :=
      match f as symbol return Sem.arguments Carrier (function_arguments symbol) -> Carrier (function_result
        symbol) with
      | Zero => fun _ => 0%Z | One => fun _ => 1%Z | TrueValue => fun _ => true
      | Read => fun a => fst a (fst (snd a))
      | Store => fun a => store (fst a) (fst (snd a)) (fst (snd (snd a)))
      | Select => fun a => if fst a then fst (snd a) else fst (snd (snd a)) end.
    Definition pr p : Sem.arguments Carrier (predicate_arguments p) -> Prop :=
      match p as symbol return Sem.arguments Carrier (predicate_arguments symbol) -> Prop with
      | Less => fun a => (fst a < fst (snd a))%Z
      | Stored => fun a => fst a (fst (snd a)) = fst (snd (snd a)) end.
    Definition interpretation := Sem.Model Carrier point fn pr.
  End Model.
  Include Core.ForModel Model.
End Kernel.
Module Export G := MakeRuleGeneration StructureSignature Kernel.
Module Export C := MakeCertification StructureSignature Kernel.
Definition xi : variable := (IntSort,0).
Definition yi : variable := (IntSort,1).
Definition flag : variable := (BoolSort,0).
Definition heap : variable := (HeapSort,0).
Definition zero := Fun Zero [].
Definition one := Fun One [].
Definition yes := Fun TrueValue [].
Definition read_at := Fun Read [Var heap;Var xi].
Definition stored_heap := Fun Store [Var heap;Var xi;one].
Definition someb {A} (x : option A) := match x with Some _ => true | None => false end.
Definition require_rule (x : option Cyclic.rule_instance) (H : someb x = true) : Cyclic.rule_instance.
Proof. destruct x; [assumption|discriminate]. Defined.
Definition requested j req (H : someb (generate_requested j req) = true) := require_rule _ H.
Definition premise_at r n := match nth_error r.(Cyclic.rule_premises) n with
  | Some p => p.(Cyclic.premise_judgment) | None => r.(Cyclic.rule_conclusion) end.
Definition assertion l a := Occ l a None.
Definition traced l a := Occ l a (Some 0).
Definition l0 := StateLabel (Base 0).

Example heterogeneous_terms : term_wfb stored_heap = true /\ term_wfb read_at = true.
Proof. split; reflexivity. Qed.
Example wrong_function_argument : term_wfb (Fun Read [yes;Var xi]) = false.
Proof. reflexivity. Qed.
Example wrong_arity : term_wfb (Fun Store [Var heap;one]) = false.
Proof. reflexivity. Qed.
Example wrong_predicate_argument : formula_wfb (Pred Less [yes;one]) = false.
Proof. reflexivity. Qed.
Example wrong_equality_sort : formula_wfb (Equal yes one) = false.
Proof. reflexivity. Qed.
Example wrong_assignment_sort : program_wfb (Assign xi yes) = false.
Proof. reflexivity. Qed.
Example wrong_update_sort : label_wfb (StateLabel (Apply (Parallel [(xi,yes)]) (Base 0))) = false.
Proof. reflexivity. Qed.
Example same_number_different_sort : variable_eqb xi flag = false.
Proof. reflexivity. Qed.
Definition vacuous := Jdg [assertion l0 (All xi Truth)] [].
Example wrong_vacuous_instantiation : someb (generate_requested vacuous (Instantiate OnLeft 0 yes)) = false.
Proof. vm_compute; reflexivity. Qed.
Example right_vacuous_instantiation : someb (generate_requested vacuous (Instantiate OnLeft 0 one)) = true.
Proof. vm_compute; reflexivity. Qed.
Example wrong_vacuous_eigenvariable : someb (generate_requested (Jdg [] [assertion l0 (All xi Truth)])
  (Eigen OnRight 0 flag)) = false.
Proof. vm_compute; reflexivity. Qed.
Example same_sort_eigenvariable : someb (generate_requested (Jdg [] [assertion l0 (All xi Truth)]) (Eigen
  OnRight 0 yi)) = true.
Proof. vm_compute; reflexivity. Qed.
Example fresh_binder_keeps_sort :
  subst_fo xi (Fun Select [Var flag;one;zero]) (All flag (Equal (Var xi) zero)) =
  All (BoolSort,1) (Equal (Fun Select [Var flag;one;zero]) zero).
Proof. reflexivity. Qed.
Definition nested_label := StateLabel (Apply (Then (Put yi one) (Parallel [(flag,yes)])) (Base 0)).
Example nested_target_eigenvariable_rejected :
  someb (generate_requested (Jdg [] [assertion nested_label (All xi Truth)]) (Eigen OnRight 0 yi)) = false.
Proof. vm_compute; reflexivity. Qed.
Definition rhs_label := StateLabel (Apply (Parallel [(heap,Fun Store [Var heap;Var yi;one])]) (Base 0)).
Example parallel_rhs_eigenvariable_rejected :
  someb (generate_requested (Jdg [] [assertion rhs_label (All xi Truth)]) (Eigen OnRight 0 yi)) = false.
Proof. vm_compute; reflexivity. Qed.
Example heap_quantifier_uses_heap_carrier s :
  fol_holds M (All heap (Equal (Var heap) (Var heap))) s <->
  forall h : Z -> Z, fol_holds M (Equal (Var heap) (Var heap)) (write M s heap (inject M HeapSort h)).
Proof. apply all_carrier; reflexivity. Qed.

Definition postcondition := Equal read_at one.
Definition updated := AssignUpdate heap stored_heap (Base 0).
Definition root := Jdg [] [traced (Join Empty l0) (Box (Assign heap stored_heap) (Next postcondition))].
Definition assign_rule := requested root (Local OnRight 0 "B.Assign.R") ltac:(vm_compute; reflexivity).
Definition with_unit := premise_at assign_rule 0.
Definition suffix_goal := Jdg [] [traced (Join l0 (StateLabel updated)) (Next postcondition)].
Definition unit_rule := requested with_unit (UnitLabels suffix_goal [false] true true) ltac:(vm_compute;
  reflexivity).
Definition suffix_rule := requested suffix_goal (Local OnRight 0 "Suffix.R") ltac:(vm_compute; reflexivity).
Definition first_leaf := Jdg [] [assertion (StateLabel updated) postcondition;assertion (StateLabel updated)
  Falsity].
Definition second_goal := premise_at suffix_rule 1.
Definition weakening := requested second_goal (Weaken OnRight 1) ltac:(vm_compute; reflexivity).
Definition final_leaf := Jdg [] [assertion (StateLabel updated) postcondition].
Lemma updated_read w : labelled_holds M w (assertion (StateLabel updated) postcondition).
Proof.
  split; [discriminate|].
  change (store (world_mapping M w 0 heap HeapSort) (world_mapping M w 0 xi IntSort) 1%Z (world_mapping M w
    0 xi IntSort) = 1%Z).
  apply read_store_same.
Qed.
Definition close_first : Cyclic.axiom_instance.
Proof.
  refine (close_pure first_leaf eq_refl eq_refl _); intros w H.
  exists (assertion (StateLabel updated) postcondition); split; [now left|apply updated_read].
Defined.
Definition close_final : Cyclic.axiom_instance.
Proof.
  refine (close_atoms final_leaf eq_refl eq_refl _); intros w H.
  exists (assertion (StateLabel updated) postcondition); split; [now left|apply updated_read].
Defined.
Definition build := Cyclic.run_script root [Cyclic.ApplyRule 0 assign_rule;Cyclic.ApplyRule 1 unit_rule;
  Cyclic.ApplyRule 2 suffix_rule;Cyclic.CloseWith 3 close_first;Cyclic.ApplyRule 4
    weakening;Cyclic.CloseWith 5 close_final].
Example accepted : Cyclic.raw_check build.(Cyclic.built_graph) empty_trace_witness = true.
Proof. vm_compute; reflexivity. Qed.
Theorem heap_assignment_reads_written_value : Cyclic.Valid root.
Proof. exact (raw_check_sound _ _ accepted). Qed.
Definition witness_world : world M.
Proof. refine (World M (fun _ _ => domain_inhabitant M) (fun _ => [fun _ => domain_inhabitant M]) _);
  discriminate. Defined.
Example nonvacuity : admissible M root witness_world.
Proof. apply judgment_wfb_admissible; reflexivity. Qed.
Print Assumptions heap_assignment_reads_written_value.
Print Assumptions all_carrier.

Definition mixed := Parallel [(xi,one);(flag,yes);(heap,stored_heap)].
Definition mixed_state := apply_update M mixed (world_mapping M witness_world 0).
Example heterogeneous_parallel_snapshot :
  mixed_state xi IntSort = 1%Z /\ mixed_state flag BoolSort = true /\
  mixed_state heap HeapSort 0%Z = 1%Z /\ mixed_state heap HeapSort 1%Z = 0%Z.
Proof. repeat split; reflexivity. Qed.

Definition heap_fresh : variable := (HeapSort,1).
Definition heap_all_root := Jdg [] [assertion l0 (All heap (Equal (Var heap) (Var heap)))].
Definition heap_all_rule := requested heap_all_root (Eigen OnRight 0 heap_fresh) ltac:(vm_compute;
  reflexivity).
Definition heap_all_leaf := Jdg [] [assertion l0 (Equal (Var heap_fresh) (Var heap_fresh))].
Definition heap_all_axiom : Cyclic.axiom_instance.
Proof.
  refine (close_atoms heap_all_leaf eq_refl eq_refl _); intros w H.
  exists (assertion l0 (Equal (Var heap_fresh) (Var heap_fresh))); split; [now left|].
  split; [discriminate|reflexivity].
Defined.
Definition heap_all_build := Cyclic.run_script heap_all_root [Cyclic.ApplyRule 0
  heap_all_rule;Cyclic.CloseWith 1 heap_all_axiom].
Theorem quantified_heap_reflexivity : Cyclic.Valid heap_all_root.
Proof. apply (raw_check_sound heap_all_build.(Cyclic.built_graph) empty_trace_witness); vm_compute;
  reflexivity. Qed.
Print Assumptions quantified_heap_reflexivity.
