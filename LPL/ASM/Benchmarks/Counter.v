(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM.Benchmarks Require Import Support.
From CyclistRocq.LPL.ASM.Cases Require Import Counter.
Import ListNotations.
Module Case := CyclistRocq.LPL.ASM.Cases.Counter.
Module Spec <: Engine.SPEC.
  Definition machine := import_machine (Case.machine).
  Definition ends := terminal_states machine.
  Definition invariant := nonnegative_state.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. intros [<-|[<-|[]]]; [apply decrement_safe|apply test_safe]. Qed.
End Spec.
Module P := Engine.ForSpec Spec.
Definition build := P.build 100 P.Contract Case.Loop.
Definition graph := P.Graph.built_graph build.
Example built : P.Graph.build_ok build = true. Proof. check_graph. Qed.
Example checked : P.Graph.raw_check graph (P.witness graph) = true. Proof. check_graph. Qed.
Example genuine_backlink : P.backlink_count graph = 1%nat. Proof. check_graph. Qed.
Theorem every_depth_safe depth : safe nonnegative_state (P.approx depth Case.Loop).
Proof. apply (P.accepted_safe graph Case.Loop eq_refl checked). Qed.
Theorem final_value_is_zero depth s tail :
  program_holds M (P.approx depth Case.Loop) (s::tail) ->
  last (s::tail) default_state 0%nat tt = 0%Z.
Proof.
  intro Hrun.
  pose proof (P.approx_source_observed depth Case.Loop s tail Hrun) as Hp.
  change (nonnegative_state s /\ True) in Hp; destruct Hp as [Hinv _].
  pose proof (P.accepted_post graph Case.Loop eq_refl checked depth s tail Hrun Hinv) as H.
  change (exists q, In q [Case.Halt] /\ observed Spec.machine q (last (s::tail) default_state)) in H.
  destruct H as [q [[<-|[]] H]].
  change (last (s::tail) default_state 0%nat tt = 0%Z /\ True) in H; tauto.
Qed.
Theorem boxed_always_nonnegative depth s : nonnegative_state s ->
  formula_holds M (Box (P.approx depth Case.Loop) (Always nonnegative)) [s].
Proof.
  intro H; exact (safety_box_always (P.approx depth Case.Loop) nonnegative s
    eq_refl (every_depth_safe depth) H).
Qed.
Theorem every_natural_input_has_a_complete_run n : forall s : state M,
  s 0%nat tt = Z.of_nat n -> exists t,
  executes (P.approx (Datatypes.S n) Case.Loop) s t /\ t 0%nat tt = 0%Z.
Proof.
  induction n as [|n IH]; intros s Hs.
  - exists s; split; [|exact Hs]. eapply seq_exec with (t:=s).
    + apply test_exec; change ((0 <= s 0%nat tt)%Z /\ True); rewrite Hs; split; [lia|exact I].
    + apply right_exec; eapply seq_exec with (t:=s).
      * apply test_exec; exact Hs.
      * apply test_exec; change (s 0%nat tt = 0%Z /\ True); auto.
  - set (s' := write M s 0 (eval_term M s (dec x))).
    assert (s' 0%nat tt = Z.of_nat n) as Hnext.
    { change (s 0%nat tt - 1 = Z.of_nat n)%Z; rewrite Hs; lia. }
    destruct (IH s' Hnext) as [t [Hrest Hzero]]. exists t; split; [|exact Hzero].
    change (executes (Seq (observe Spec.machine Case.Loop)
      (Choice (Seq (Seq (Test Case.positive) (Assign 0 (dec x))) (P.approx (Datatypes.S n) Case.Loop))
              (Seq (Test iszero) (P.approx (Datatypes.S n) Case.Halt)))) s t).
    eapply seq_exec with (t:=s).
    + apply test_exec; change ((0 <= s 0%nat tt)%Z /\ True); rewrite Hs; split; [lia|exact I].
    + apply left_exec; eapply seq_exec with (t:=s'); [|exact Hrest].
      eapply seq_exec with (t:=s); [apply test_exec; change (0 < s 0%nat tt)%Z; rewrite Hs; lia|].
      apply assignment_exec.
Qed.
Print Assumptions every_depth_safe.
Print Assumptions final_value_is_zero.
Print Assumptions boxed_always_nonnegative.
Print Assumptions every_natural_input_has_a_complete_run.

Goal True.
  let nodes := eval vm_compute in (List.length (P.Graph.graph_nodes graph)) in
  let links := eval vm_compute in (P.backlink_count graph) in
  idtac "GRAPH Counter" nodes links; exact I.
Qed.
