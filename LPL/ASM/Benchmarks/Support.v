(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** Shared kernel and case declarations for local continuation proofs. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM Require Export Support.
From CyclistRocq.LPL.ASM Require Export Continuations.
Import ListNotations.
Module Engine := MakeContinuations ZSignature ZKernel.

(** Transport only the generative record wrappers. Control types, formulas,
    terms, instructions, enumeration, and initial state are reused exactly. *)
Definition import_machine (m : Theory.A.ASM) : Engine.Base.A.ASM :=
  Engine.Base.A.Machine (Theory.A.ASM_STATE m) (Theory.A.state_eq_dec m)
    (Theory.A.states m) (Theory.A.states_complete m) (Theory.A.states_unique m)
    (fun q => Engine.Base.A.StateDescription
      (Theory.A.propositions (Theory.A.description m q)))
    (map (fun e => Engine.Base.A.Transition (Theory.A.source e)
      (Theory.A.target e) (Theory.A.instruction e)) (Theory.A.transitions m))
    (Theory.A.initial m).
Export Engine.Base.
Lemma imported_description m q :
  state_assertion (description (import_machine m) q) =
    Theory.A.state_assertion (Theory.A.description m q).
Proof. reflexivity. Qed.
Lemma imported_edges m :
  map (fun e => (source e,target e,instruction e)) (transitions (import_machine m)) =
  map (fun e => (Theory.A.source e,Theory.A.target e,Theory.A.instruction e)) (Theory.A.transitions m).
Proof. unfold import_machine; cbn [transitions]; rewrite map_map; reflexivity. Qed.

Lemma trivially_safe p : safe (fun _ : state M => True) p.
Proof. intros s tail Hrun _; apply Forall_forall; auto. Qed.

(** These tactics only close reflected graph checks, not semantic goals. *)
Ltac check_graph := vm_compute; reflexivity.

Lemma safety_box_always p a s : pureb a = true -> safe (fol_holds M a) p ->
  fol_holds M a s -> formula_holds M (Box p (Always a)) [s].
Proof.
  intros Hpure Hsafe Hinitial execution result Hexec Ho.
  apply overlap_list_singleton in Ho as [tail [Heq ->]]; subst execution.
  apply always_pure_forall; [exact Hpure|discriminate|].
  eapply Forall_impl; [|exact (Hsafe s tail Hexec Hinitial)].
  intros start H; now rewrite (pure_head M a Hpure).
Qed.
