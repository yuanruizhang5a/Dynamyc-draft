(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** Shared integer kernel and small LPL execution/invariant proof helpers. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.Benchmarks Require Export Support.
From CyclistRocq.LPL.ASM Require Import Properties.
Import ListNotations.
Module Export Theory := MakeASMProperties ZSignature ZKernel.

(** Merely abbreviates an existential trace in LPL's existing semantics.
    The middle list retains every test/iteration stutter. *)
Definition executes p (s t : state M) :=
  exists middle, program_holds M p (s :: middle ++ [t]).
Lemma test_exec a s : formula_holds M a [s;s] -> executes (Test a) s s.
Proof. intro H; exists []; exists s; auto. Qed.
Lemma assignment_exec x t s : executes (Assign x t) s (write M s x (eval_term M s t)).
Proof. exists []; exists s; reflexivity. Qed.
Lemma seq_exec p q s t u : executes p s t -> executes q t u -> executes (Seq p q) s u.
Proof.
  intros [xs Hp] [ys Hq]; exists (xs ++ t :: ys).
  exists (s :: xs ++ [t]), (t :: ys ++ [u]); split; [exact Hp|].
  split; [exact Hq|]. exists (s::xs), t, (ys++[u]); repeat split; cbn; auto.
  now rewrite <- app_assoc.
Qed.
Lemma left_exec p q s t : executes p s t -> executes (Choice p q) s t.
Proof. intros [xs H]; exists xs; now left. Qed.
Lemma right_exec p q s t : executes q s t -> executes (Choice p q) s t.
Proof. intros [xs H]; exists xs; now right. Qed.
Definition nonnegative_state (s : state M) := (0 <= s 0%nat tt)%Z.
Lemma increment_safe : safe nonnegative_state (Assign 0 (inc x)).
Proof.
  intros s tail [start Heq] H; injection Heq as Hs Htail; subst.
  constructor; [exact H|]. constructor; [|constructor].
  change (0 <= start 0%nat tt + 1)%Z. unfold nonnegative_state in H; lia.
Qed.
Lemma set_one_safe : safe nonnegative_state (Assign 0 one).
Proof.
  intros s tail [start Heq] H; injection Heq as Hs Htail; subst.
  constructor; [exact H|]. constructor; [|constructor]. change (0 <= 1)%Z; lia.
Qed.
Lemma set_zero_safe : safe nonnegative_state (Assign 0 zero).
Proof.
  intros s tail [start Heq] H; injection Heq as Hs Htail; subst.
  constructor; [exact H|]. constructor; [|constructor]. change (0 <= 0)%Z; lia.
Qed.
Lemma decrement_safe : safe nonnegative_state
  (Seq (Test (Pred 2 [zero;x])) (Assign 0 (dec x))).
Proof.
  intros s tail [a [b [[start [Ha Hguard]] [[start' Hb] Ho]]]] H.
  subst a b. apply (overlap_snoc M [start] start start') in Ho.
  destruct Ho as [Heq Htrace]; subst start'.
  change (s::tail = [start;start;write M start 0 (eval_term M start (dec x))]) in Htrace.
  injection Htrace as Hs Htail; subst.
  change (0 < start 0%nat tt)%Z in Hguard.
  repeat constructor; unfold nonnegative_state in *; try assumption.
  change (0 <= start 0%nat tt - 1)%Z; lia.
Qed.
