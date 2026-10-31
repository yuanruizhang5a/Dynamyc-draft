(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM.Benchmarks Require Import Support.
From CyclistRocq.LPL.ASM.Cases Require Import StraightLine.
Import ListNotations.
Module Case := CyclistRocq.LPL.ASM.Cases.StraightLine.
Module Spec <: Engine.SPEC.
  Definition machine := import_machine (Case.machine).
  Definition ends := terminal_states machine.
  Definition invariant := nonnegative_state.
  Lemma checked_machine : asm_wfb machine = true.
  Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. intros [<-|[<-|[]]]; [apply set_one_safe|apply increment_safe]. Qed.
End Spec.
Module P := Engine.ForSpec Spec.
Definition build := P.build 100 P.Contract Case.Start.
Definition graph := P.Graph.built_graph build.
Example built : P.Graph.build_ok build = true. Proof. check_graph. Qed.
Example checked : P.Graph.raw_check graph (P.witness graph) = true. Proof. check_graph. Qed.
Example acyclic : P.backlink_count graph = 0%nat. Proof. check_graph. Qed.
Theorem every_depth_safe depth : safe nonnegative_state (P.approx depth Case.Start).
Proof. apply (P.accepted_safe graph Case.Start eq_refl checked). Qed.
Theorem final_value_is_two depth s tail :
  program_holds M (P.approx depth Case.Start) (s::tail) ->
  last (s::tail) default_state 0%nat tt = 2%Z.
Proof.
  intro Hrun.
  pose proof (P.approx_source_observed depth Case.Start s tail Hrun) as Hsource.
  change (s 0%nat tt = 0%Z /\ (s 0%nat tt = 0%Z /\ True)) in Hsource.
  assert (nonnegative_state s) as Hinv by (unfold nonnegative_state; lia).
  pose proof (P.accepted_post graph Case.Start eq_refl checked depth s tail Hrun Hinv) as H.
  change (exists q, In q [Case.Done] /\ observed Spec.machine q (last (s::tail) default_state)) in H.
  destruct H as [q [[<-|[]] H]].
  change (last (s::tail) default_state 0%nat tt = 2%Z /\ True) in H; tauto.
Qed.
Definition s0 := constant_state 0.
Definition s1 := write M s0 0 (eval_term M s0 one).
Definition s2 := write M s1 0 (eval_term M s1 (inc x)).
Theorem concrete_execution : executes (P.approx 2 Case.Start) s0 s2.
Proof.
  eapply seq_exec with (t:=s0); [apply test_exec; vm_compute; intuition discriminate|].
  eapply seq_exec with (t:=s1); [apply assignment_exec|].
  eapply seq_exec with (t:=s1); [apply test_exec; vm_compute; intuition discriminate|].
  eapply seq_exec with (t:=s2); [apply assignment_exec|].
  apply test_exec; vm_compute; intuition discriminate.
Qed.
Theorem wrong_source_values_rejected depth tail :
  ~ program_holds M (P.approx depth Case.Start) (constant_state 1::tail).
Proof.
  intro H; pose proof (P.approx_source_observed depth Case.Start _ _ H) as Hp.
  change (1%Z=0%Z /\ (1%Z=0%Z /\ True)) in Hp; destruct Hp as [Hbad _]; discriminate.
Qed.
Example syntax_checked depth : program_wfb (P.approx depth Case.Start) = true.
Proof. apply P.approx_checked. Qed.
Print Assumptions every_depth_safe.
Print Assumptions final_value_is_two.
Print Assumptions concrete_execution.

Goal True.
  let nodes := eval vm_compute in (List.length (P.Graph.graph_nodes graph)) in
  let links := eval vm_compute in (P.backlink_count graph) in
  idtac "GRAPH StraightLine" nodes links; exact I.
Qed.
