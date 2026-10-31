(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM.Benchmarks Require Import Support.
From CyclistRocq.LPL.ASM.Cases Require Import Cycle.
Import ListNotations.
Module Case := CyclistRocq.LPL.ASM.Cases.Cycle.
Module PrefixSpec <: Engine.SPEC.
  Definition machine := import_machine (Case.machine).
  Definition ends := states machine.
  Definition invariant := nonnegative_state.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. intros [<-|[<-|[]]]; [apply set_one_safe|apply set_zero_safe]. Qed.
End PrefixSpec.
Module TerminalSpec <: Engine.SPEC.
  Definition machine := import_machine (Case.machine).
  Definition ends := terminal_states machine.
  Definition invariant (_ : state M) := True.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. intro; apply trivially_safe. Qed.
End TerminalSpec.
Module P := Engine.ForSpec PrefixSpec.
Module T := Engine.ForSpec TerminalSpec.
Definition graph := P.Graph.built_graph (P.build 100 P.Contract Case.Tick).
Definition terminal_graph := T.Graph.built_graph (T.build 100 T.Contract Case.Tick).
Example checked : P.Graph.raw_check graph (P.witness graph) = true. Proof. check_graph. Qed.
Example checked_terminal : T.Graph.raw_check terminal_graph (T.witness terminal_graph) = true.
Proof. check_graph. Qed.
Example actual_backlink : P.backlink_count graph = 1%nat. Proof. check_graph. Qed.
Theorem finite_prefixes_safe depth : safe nonnegative_state (P.approx depth Case.Tick).
Proof. apply (P.accepted_safe graph Case.Tick eq_refl checked). Qed.
Theorem no_complete_execution depth tr : ~ program_holds M (T.approx depth Case.Tick) tr.
Proof.
  destruct tr as [|s tail]; intro H.
  - pose proof (program_length M _ _ H); cbn in H0; lia.
  - pose proof (T.accepted_post terminal_graph Case.Tick eq_refl checked_terminal depth s tail H I) as Hp.
    change (exists q, In q [] /\ observed TerminalSpec.machine q (last (s::tail) default_state)) in Hp.
    destruct Hp as [q [Hfalse _]]; contradiction.
Qed.
Definition s0 := constant_state 0.
Definition s1 := write M s0 0 (zvalue 1).
Theorem arbitrarily_many_rounds n : executes (P.approx (2*n) Case.Tick) s0 s0.
Proof.
  assert (write M s1 0 (zvalue 0) = s0) as Hback.
  { unfold s1; rewrite write_shadow; apply write_current. }
  induction n as [|n IH].
  - apply test_exec; vm_compute; intuition discriminate.
  - replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2*n))) by lia.
    change (executes (Choice (P.stop Case.Tick)
      (Seq (observe PrefixSpec.machine Case.Tick) (Seq (Assign 0 one)
        (P.approx (Datatypes.S (2*n)) Case.Tock)))) s0 s0).
    apply right_exec; eapply seq_exec with (t:=s0).
    + apply test_exec; vm_compute; intuition discriminate.
    + eapply seq_exec with (t:=s1); [apply assignment_exec|].
      change (executes (Choice (P.stop Case.Tock)
        (Seq (observe PrefixSpec.machine Case.Tock) (Seq (Assign 0 zero)
          (P.approx (2*n) Case.Tick)))) s1 s0).
      apply right_exec; eapply seq_exec with (t:=s1).
      * apply test_exec; vm_compute; intuition discriminate.
      * eapply seq_exec with (t:=s0); [rewrite <- Hback; apply assignment_exec|exact IH].
Qed.
Print Assumptions finite_prefixes_safe.
Print Assumptions no_complete_execution.
Print Assumptions arbitrarily_many_rounds.

Goal True.
  let nodes := eval vm_compute in (List.length (P.Graph.graph_nodes graph)) in
  let links := eval vm_compute in (P.backlink_count graph) in
  idtac "GRAPH PrefixCycle" nodes links; exact I.
Qed.
Goal True.
  let nodes := eval vm_compute in (List.length (T.Graph.graph_nodes terminal_graph)) in
  let links := eval vm_compute in (T.backlink_count terminal_graph) in
  idtac "GRAPH TerminalCycle" nodes links; exact I.
Qed.
