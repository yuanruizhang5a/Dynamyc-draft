(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * Primitive syntax, derived aliases, and direct local rule recognition

    Each alias is definitionally equal to its primitive expansion. In
    particular Disj a b is also Impl (Neg a) b, so a local scan must offer
    both derived rules together with the primitive negation rule. The
    executable examples below protect that interface and the empty-trace,
    typed-substitution and occurrence-tag boundaries. *)
From Stdlib Require Import List Bool String.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.

(** An exhaustive match lists precisely the nine formula constructors. *)
Fixpoint primitive_size (a : formula) : nat :=
  match a with
  | Truth | Pred _ _ | EqualAt _ _ _ => 1
  | Neg a | All _ a | First a | Box _ a => S (primitive_size a)
  | Conj a b | Suffix a b => S (primitive_size a + primitive_size b)
  end.
Example falsity_expansion : Falsity = Neg Truth.
Proof. reflexivity. Qed.
Example disjunction_expansion a b : Disj a b = Neg (Conj (Neg a) (Neg b)).
Proof. reflexivity. Qed.
Example implication_expansion a b : Impl a b = Neg (Conj a (Neg b)).
Proof. reflexivity. Qed.
Example existential_expansion u a : Ex u a = Neg (All u (Neg a)).
Proof. reflexivity. Qed.
Example dual_suffix_expansion a b : DualSuffix a b = Neg (Suffix (Neg a) (Neg b)).
Proof. reflexivity. Qed.
Example diamond_expansion p a : Diamond p a = Neg (Box p (Neg a)).
Proof. reflexivity. Qed.
Example aliases_can_overlap a b : Disj a b = Impl (Neg a) b.
Proof. reflexivity. Qed.

Definition modal := Box (Test Truth) Truth.
Definition root := Jdg [] [assertion l0 (Disj modal modal)].
Example all_overlapping_rules_are_offered :
  map Cyclic.rule_name (generate_rules root) = ["Not.R";"Or.R";"Impl.R"].
Proof. vm_compute; reflexivity. Qed.
Example requested_derived_rule : someb (generate_requested root (Local OnRight 0 "Or.R")) = true.
Proof. vm_compute; reflexivity. Qed.
Example requested_primitive_rule : someb (generate_requested root (Local OnRight 0 "Not.R")) = true.
Proof. vm_compute; reflexivity. Qed.
Example requested_other_derived_rule : someb (generate_requested root (Local OnRight 0 "Impl.R")) = true.
Proof. vm_compute; reflexivity. Qed.
Definition left_root := Jdg [assertion l0 (Disj modal modal)] [].
Example all_overlapping_left_rules_are_offered :
  map Cyclic.rule_name (generate_rules left_root) = ["Not.L";"Or.L";"Impl.L"].
Proof. vm_compute; reflexivity. Qed.
Example requested_left_disjunction :
  someb (generate_requested left_root (Local OnLeft 0 "Or.L")) = true.
Proof. vm_compute; reflexivity. Qed.
Example requested_left_negation :
  someb (generate_requested left_root (Local OnLeft 0 "Not.L")) = true.
Proof. vm_compute; reflexivity. Qed.
Example requested_left_implication :
  someb (generate_requested left_root (Local OnLeft 0 "Impl.L")) = true.
Proof. vm_compute; reflexivity. Qed.

Example existential_capture_avoidance :
  subst_fo 0 y (Ex 1 (Equal x y)) = Ex 2 (Equal y (Var 2)).
Proof. reflexivity. Qed.
Example derived_quantifier_rejects_modal_body :
  formula_wfb (Ex 0 modal) = false.
Proof. reflexivity. Qed.
Example derived_quantifier_rejects_temporal_body :
  formula_wfb (Ex 0 (Next Truth)) = false.
Proof. reflexivity. Qed.
Example modal_outside_derived_quantifier :
  formula_wfb (Diamond (Test Truth) (Ex 0 (Equal x x))) = true.
Proof. reflexivity. Qed.
Example derived_dual_remains_traceable : traceableb (DualSuffix Truth Truth) = true.
Proof. reflexivity. Qed.
Example expanded_dual_remains_traceable : traceableb (Neg (Suffix (Neg Truth) (Neg Truth))) = true.
Proof. reflexivity. Qed.
Example derived_diamond_is_not_traceable : traceableb (Diamond (Test Truth) Truth) = false.
Proof. reflexivity. Qed.
Example arbitrary_negative_suffix_is_not_traceable : traceableb (Neg (Suffix Truth Truth)) = false.
Proof. reflexivity. Qed.

Example aliases_are_false_on_empty :
  ~ formula_holds M (Disj Truth Truth) [] /\
  ~ formula_holds M (Impl Truth Truth) [] /\
  ~ formula_holds M (Ex 0 Truth) [] /\
  ~ formula_holds M (DualSuffix Truth Truth) [] /\
  ~ formula_holds M (Diamond (Test Truth) Truth) [].
Proof. repeat split; apply empty_trace_false. Qed.
Example all_formulas_are_false_on_empty a : ~ formula_holds M a [].
Proof. apply empty_trace_false. Qed.
Example derived_diamond_native_meaning p a tr : tr <> [] ->
  (formula_holds M (Diamond p a) tr <-> exists execution result,
   program_holds M p execution /\ overlap M tr execution result /\ formula_holds M a result).
Proof. apply diamond_holds. Qed.
Example derived_existential_native_meaning u a tr : tr <> [] ->
  (formula_holds M (Ex u a) tr <-> exists d,
   formula_holds M a (map (fun s => write M s u d) tr)).
Proof. apply ex_holds. Qed.
Print Assumptions generate_rules_spec.
Print Assumptions diamond_holds.
Print Assumptions subst_fo_correct.
