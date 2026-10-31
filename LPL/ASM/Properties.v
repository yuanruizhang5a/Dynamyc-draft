(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * Properties of one-step LPL unfoldings

    These are the existing LPL semantics throughout: no independent ASM
    semantics, fairness assumption, or infinite-run interpretation is added. *)
From Stdlib Require Import List Bool Arith.
From CyclistRocq.LPL Require Import Signature Rules.
From CyclistRocq.LPL.ASM Require Import Syntax.
Import ListNotations.

Module MakeASMProperties (S : SIGNATURE) (Kernel : KERNEL S).
Module Export A := MakeASM S Kernel.
Module Export K := Kernel.

(** Safety means every visited valuation, including tests and final
    stutters, satisfies the invariant when the first valuation does. *)
Definition relation_safe (Inv : state M -> Prop) (R : list (state M) -> Prop) :=
  forall s tail, R (s :: tail) -> Inv s -> Forall Inv (s :: tail).
Definition safe Inv (p : program) := relation_safe Inv (program_holds M p).

Lemma test_safe Inv a : safe Inv (Test a).
Proof.
  intros s tail [start [Heq _]] H; injection Heq as Hs Htail; subst.
  repeat constructor; exact H.
Qed.
Lemma compose_safe Inv R T : relation_safe Inv R -> relation_safe Inv T ->
  relation_safe Inv (compose M R T).
Proof.
  intros Hp Hq s tail [a [b [Ha [Hb Ho]]]] Hs.
  destruct (overlap_list_head _ _ _ Ho) as [head [arest [ct [Hfirst Hresult]]]].
  injection Hresult as Hhead Htail; subst head a.
  pose proof (Hp s arest Ha Hs) as Hsafe.
  destruct Ho as [prefix [middle [bt [Haend [Hbstart Hout]]]]].
  assert (Inv middle) as Hmiddle.
  { rewrite Forall_forall in Hsafe. apply Hsafe. rewrite Haend.
    apply in_app_iff; cbn; auto. }
  rewrite Hbstart in Hb. pose proof (Hq middle bt Hb Hmiddle) as HsafeB.
  rewrite Hout, Forall_app. rewrite Haend, Forall_app in Hsafe.
  tauto.
Qed.
Lemma seq_safe Inv p q : safe Inv p -> safe Inv q -> safe Inv (Seq p q).
Proof. apply compose_safe. Qed.
Lemma choice_safe Inv p q : safe Inv p -> safe Inv q -> safe Inv (Choice p q).
Proof. intros Hp Hq s tail [H|H] Hs; [eapply Hp|eapply Hq]; eauto. Qed.
Lemma star_safe Inv p : safe Inv p -> safe Inv (Star p).
Proof.
  intros Hp s tail [n Hpower] Hs.
  assert (forall n s tail, finite_power M (program_holds M p) n (s::tail) ->
    Inv s -> Forall Inv (s::tail)) as Hn.
  { intro count; induction count as [|count IH]; intros start rest H Hstart.
    - destruct H as [t Heq]; injection Heq as Hs' Ht; subst.
      repeat constructor; exact Hstart.
    - exact (compose_safe Inv _ _ Hp IH start rest H Hstart).
  }
  eapply Hn; eauto.
Qed.

(** A local safety rule requires safety of the target continuations.
    Global cyclic contracts are established in [Continuations.v]. *)
Lemma alternative_safe Inv a b :
  (match a with None => True | Some p => safe Inv p end) ->
  (match b with None => True | Some p => safe Inv p end) ->
  match alternative a b with None => True | Some p => safe Inv p end.
Proof. destruct a,b; cbn; auto using choice_safe. Qed.
Theorem unfold_at_safe Inv m continuation q :
  (forall e, In e (transitions m) -> safe Inv (instruction e)) ->
  (forall r, safe Inv (continuation r)) -> safe Inv (unfold_at m continuation q).
Proof.
  intros He Hk; apply seq_safe; [apply test_safe|].
  assert (forall ps, Forall (fun p => match p with None => True | Some p => safe Inv p end) ps ->
    safe Inv (materialize (alternatives ps))) as Hchoices.
  { intros ps Hps.
    assert (match alternatives ps with None => True | Some p => safe Inv p end) as H.
    { induction Hps; [exact I|]. cbn [alternatives]. now apply alternative_safe. }
    destruct (alternatives ps); cbn in *; auto using test_safe. }
  apply Hchoices, Forall_forall; intros p Hp.
  apply in_map_iff in Hp as [e [<- Hin]].
  destruct (state_eqb m q (source e)); cbn; [|exact I].
  apply seq_safe; [now apply He|apply Hk].
Qed.
Theorem unfold_at_source_observed m continuation q s tail :
  program_holds M (unfold_at m continuation q) (s::tail) ->
  formula_holds M (state_assertion (description m q)) [s;s].
Proof.
  intros [a [b [[start [Ha Hguard]] [Hb Ho]]]]; subst a.
  destruct (overlap_list_head _ _ _ Ho) as [head [arest [ct [Heq Hout]]]].
  injection Heq as Hhead Hat; injection Hout as Hs Htail; subst; exact Hguard.
Qed.

(** A postcondition here is a fact about the last LPL valuation, not a new
    ASM execution relation. Unlike [Box p a], it really observes the end. *)
Definition default_state : state M := fun _ => domain_inhabitant M.
Definition post (P : state M -> Prop) p :=
  forall tr, program_holds M p tr -> P (last tr default_state).
Definition observed m q s := formula_holds M (state_assertion (description m q)) [s;s].

End MakeASMProperties.
