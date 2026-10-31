(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * Finite abstract state machines with one-step LPL unfolding

    State descriptions contain only propositions. Observations are tests,
    and updates occur only in transition instructions. Reuse the caller's
    kernel and interpret unfolded programs using LPL's [program_holds]. *)
From Stdlib Require Import List Bool Arith.
From CyclistRocq.LPL Require Import Signature Rules.
Import ListNotations.

Module MakeASM (S : SIGNATURE) (Kernel : KERNEL S).
Module Export Sem := Kernel.Core.Pr.Sem.
Module Export Syn := Sem.Syn.

Record state_description := StateDescription {
  propositions : list formula
}.

Fixpoint conjunction (xs : list formula) : formula :=
  match xs with [] => Truth | a :: rest => Conj a (conjunction rest) end.

(** Lists represent finite sets of propositions. Duplicates are harmless;
    an empty description asserts [Truth]. *)
Definition state_assertion (d : state_description) : formula :=
  conjunction (propositions d).

Record transition (Q : Type) := Transition {
  source : Q;
  target : Q;
  instruction : program
}.
Arguments Transition {Q}.
Arguments source {Q}.
Arguments target {Q}.
Arguments instruction {Q}.

(** The common cases have exactly the requested assignment/test shapes.
    [Transition] also permits a user-specified regular LPL instruction. *)
Definition unconditional {Q} (s t : Q) x value : transition Q :=
  Transition s t (Assign x value).
Definition conditional {Q} (s t : Q) guard body : transition Q :=
  Transition s t (Seq (Test guard) body).
Definition guarded {Q} (s t : Q) guard : transition Q :=
  Transition s t (Test guard).

Record ASM := Machine {
  ASM_STATE : Type;
  state_eq_dec : forall s t : ASM_STATE, {s = t} + {s <> t};
  states : list ASM_STATE;
  states_complete : forall q, In q states;
  states_unique : NoDup states;
  description : ASM_STATE -> state_description;
  transitions : list (transition ASM_STATE);
  initial : ASM_STATE
}.
Arguments ASM_STATE _ : clear implicits.

Definition state_eqb (m : ASM) (s t : ASM_STATE m) :=
  if state_eq_dec m s t then true else false.
Lemma state_eqb_spec m s t : state_eqb m s t = true <-> s = t.
Proof. unfold state_eqb; destruct (state_eq_dec m s t); intuition discriminate. Qed.

Definition observe m (q : ASM_STATE m) := Test (state_assertion (description m q)).
(** [None] represents the empty outgoing choice, never a successful test. *)
Definition alternative (a b : option program) : option program :=
  match a, b with
  | None, _ => b | _, None => a | Some p, Some q => Some (Choice p q)
  end.
Fixpoint alternatives (ps : list (option program)) : option program :=
  match ps with [] => None | p :: rest => alternative p (alternatives rest) end.
Definition materialize (p : option program) : program :=
  match p with Some p => p | None => Test Falsity end.

Definition terminalb m (q : ASM_STATE m) :=
  negb (existsb (fun e => state_eqb m q (source e)) (transitions m)).
Definition terminal_states m := filter (terminalb m) (states m).

(** Open exactly one layer: observe the source, then choose an outgoing
    instruction followed by its supplied target continuation. A dead end
    blocks; endpoint stopping is handled by the continuation proof layer. *)
Definition unfold_at m (continuation : ASM_STATE m -> program) (s : ASM_STATE m) :=
  Seq (observe m s)
    (materialize (alternatives (map (fun e =>
      if state_eqb m s (source e)
      then Some (Seq (instruction e) (continuation (target e))) else None)
      (transitions m)))).

Definition description_wfb d := formula_wfb (state_assertion d) && pureb (state_assertion d).
Definition asm_wfb m :=
  forallb (fun q => description_wfb (description m q)) (states m) &&
  forallb (fun e => program_wfb (instruction e)) (transitions m).

(** Syntax preservation is proved compositionally, rather than trusting
    computation of individual benchmark instances. *)
Lemma seq_wfb p q : program_wfb p = true -> program_wfb q = true ->
  program_wfb (Seq p q) = true.
Proof. unfold program_wfb; cbn; rewrite !andb_true_iff; tauto. Qed.
Lemma choice_wfb p q : program_wfb p = true -> program_wfb q = true ->
  program_wfb (Choice p q) = true.
Proof. unfold program_wfb; cbn; rewrite !andb_true_iff; tauto. Qed.
Lemma star_wfb p : program_wfb p = true -> program_wfb (Star p) = true.
Proof. exact (fun H => H). Qed.
Definition option_wf (p : option program) :=
  match p with None => True | Some p => program_wfb p = true end.
Lemma alternative_wf a b : option_wf a -> option_wf b -> option_wf (alternative a b).
Proof. destruct a, b; cbn; auto using choice_wfb. Qed.
Lemma alternatives_wf ps : Forall option_wf ps -> option_wf (alternatives ps).
Proof. intro H; induction H; cbn; auto using alternative_wf. Qed.
Lemma materialize_wf p : option_wf p -> program_wfb (materialize p) = true.
Proof. destruct p; cbn; auto. Qed.
Lemma observe_wf m q : asm_wfb m = true -> program_wfb (observe m q) = true.
Proof.
  unfold asm_wfb; rewrite andb_true_iff; intros [H _].
  pose proof (proj1 (forallb_forall _ _) H q (states_complete m q)) as Hd.
  unfold description_wfb in Hd; apply andb_true_iff in Hd as [Hd _]. exact Hd.
Qed.
Lemma instruction_wf m e : asm_wfb m = true -> In e (transitions m) ->
  program_wfb (instruction e) = true.
Proof.
  unfold asm_wfb; rewrite andb_true_iff; intros [_ H] Hin.
  exact (proj1 (forallb_forall _ _) H e Hin).
Qed.
Theorem unfold_at_wf m continuation q : asm_wfb m = true ->
  (forall r, program_wfb (continuation r) = true) ->
  program_wfb (unfold_at m continuation q) = true.
Proof.
  intros Hm Hk; apply seq_wfb; [now apply observe_wf|].
  apply materialize_wf, alternatives_wf, Forall_forall; intros p Hp.
  apply in_map_iff in Hp as [e [<- Hin]].
  destruct (state_eqb m q (source e)); [|exact I].
  apply seq_wfb; [eapply instruction_wf; eauto|apply Hk].
Qed.

End MakeASM.
