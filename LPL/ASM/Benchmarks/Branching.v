(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM.Benchmarks Require Import Support.
From CyclistRocq.LPL.ASM.Cases Require Import Branching.
Import ListNotations.
Module Case := CyclistRocq.LPL.ASM.Cases.Branching.
Module NondeterministicSpec <: Engine.SPEC.
  Definition machine := import_machine (Case.machine_with false).
  Definition ends := terminal_states machine.
  Definition invariant := nonnegative_state.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. intros [<-|[<-|[]]]; [apply set_zero_safe|apply set_one_safe]. Qed.
End NondeterministicSpec.
Module ConditionalSpec <: Engine.SPEC.
  Definition machine := import_machine (Case.machine_with true).
  Definition ends := terminal_states machine.
  Definition invariant := nonnegative_state.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof.
    intros [<-|[<-|[]]]; apply seq_safe; try apply test_safe;
      [apply set_zero_safe|apply set_one_safe].
  Qed.
End ConditionalSpec.
Module N := Engine.ForSpec NondeterministicSpec.
Module C := Engine.ForSpec ConditionalSpec.
Definition ng := N.Graph.built_graph (N.build 100 N.Contract Case.Choose).
Definition cg := C.Graph.built_graph (C.build 100 C.Contract Case.Choose).
Example nondeterministic_checked : N.Graph.raw_check ng (N.witness ng) = true.
Proof. check_graph. Qed.
Example conditional_checked : C.Graph.raw_check cg (C.witness cg) = true.
Proof. check_graph. Qed.
Theorem nondeterministic_safe depth : safe nonnegative_state (N.approx depth Case.Choose).
Proof. apply (N.accepted_safe ng Case.Choose eq_refl nondeterministic_checked). Qed.
Theorem conditional_safe depth : safe nonnegative_state (C.approx depth Case.Choose).
Proof. apply (C.accepted_safe cg Case.Choose eq_refl conditional_checked). Qed.
Theorem both_nondeterministic_outcomes :
  executes (N.approx 1 Case.Choose) (constant_state 0) (write M (constant_state 0) 0 (zvalue 0)) /\
  executes (N.approx 1 Case.Choose) (constant_state 0) (write M (constant_state 0) 0 (zvalue 1)).
Proof.
  split; eapply seq_exec with (t:=constant_state 0).
  - apply test_exec; exact I.
  - apply left_exec; eapply seq_exec; [apply assignment_exec|].
    apply test_exec; vm_compute; intuition discriminate.
  - apply test_exec; exact I.
  - apply right_exec; eapply seq_exec; [apply assignment_exec|].
    apply test_exec; vm_compute; intuition discriminate.
Qed.
Theorem conditional_zero_branch : executes (C.approx 1 Case.Choose)
  (constant_state 0) (write M (constant_state 0) 0 (zvalue 0)).
Proof.
  eapply seq_exec with (t:=constant_state 0); [apply test_exec; exact I|].
  apply left_exec; eapply seq_exec.
  - eapply seq_exec with (t:=constant_state 0); [apply test_exec; reflexivity|apply assignment_exec].
  - apply test_exec; vm_compute; intuition discriminate.
Qed.
Theorem conditional_nonzero_branch : executes (C.approx 1 Case.Choose)
  (constant_state 7) (write M (constant_state 7) 0 (zvalue 1)).
Proof.
  eapply seq_exec with (t:=constant_state 7); [apply test_exec; exact I|].
  apply right_exec; eapply seq_exec.
  - eapply seq_exec with (t:=constant_state 7).
    + apply test_exec; change (7%Z <> 0%Z); discriminate.
    + apply assignment_exec.
  - apply test_exec; vm_compute; intuition discriminate.
Qed.
Theorem wrong_guard_blocks_assignment tr :
  ~ program_holds M (Seq (Test iszero) (Assign 0 zero)) (constant_state 7::tr).
Proof.
  intros [a [b [[s [Ha Hguard]] [Hb Ho]]]]; subst a.
  destruct (overlap_list_head _ _ _ Ho) as [head [arest [ct [Heq Hout]]]].
  injection Heq as Hhead Htail; injection Hout as Hs Hrest; subst.
  change (7%Z=0%Z) in Hguard; discriminate.
Qed.
Print Assumptions nondeterministic_safe.
Print Assumptions conditional_safe.
Print Assumptions conditional_nonzero_branch.

Goal True.
  let nodes := eval vm_compute in (List.length (N.Graph.graph_nodes ng)) in
  let links := eval vm_compute in (N.backlink_count ng) in
  idtac "GRAPH Nondeterministic" nodes links; exact I.
Qed.
Goal True.
  let nodes := eval vm_compute in (List.length (C.Graph.graph_nodes cg)) in
  let links := eval vm_compute in (C.backlink_count cg) in
  idtac "GRAPH Conditional" nodes links; exact I.
Qed.
