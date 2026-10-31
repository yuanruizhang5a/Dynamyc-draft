(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * Reified syntax and its executable checks

    This file defines data, not truth in a model. Read it in four parts:
    terms and mutually defined formulas/programs; named FOL substitution;
    updates and labels; occurrences, judgments and reflected syntax checks.
    Formulas have nine primitive constructors. Derived aliases are defined
    near the start of the file; generators match their expansions directly.
    Semantics.v gives these objects meanings, and RuleGeneration.v uses the
    Boolean checks to construct rules together with their required evidence.

    Names ending in [b] return Booleans; later [_spec] lemmas connect those
    computations to propositions. [Defined] keeps equality decisions and
    other computational proofs transparent so generators can reduce them. *)
From Stdlib Require Import List Bool Arith Lia.
From CyclistRocq.LPL Require Import Signature.
Import ListNotations.

Module MakeSyntax (S : SIGNATURE).

Definition variable := (S.sort * nat)%type.
Definition variable_eq_dec : forall x y : variable, {x=y}+{x<>y}.
Proof. decide equality; [apply Nat.eq_dec|apply S.sort_eq_dec]. Defined.
Definition variable_eqb (x y : variable) := if variable_eq_dec x y then true else false.
Lemma variable_eqb_eq x y : variable_eqb x y = true <-> x=y.
Proof. unfold variable_eqb; destruct (variable_eq_dec x y); intuition discriminate. Qed.
Lemma variable_eqb_neq x y : variable_eqb x y = false <-> x<>y.
Proof. unfold variable_eqb; destruct (variable_eq_dec x y); intuition discriminate. Qed.
Lemma variable_eqb_refl x : variable_eqb x x = true.
Proof. apply variable_eqb_eq; reflexivity. Qed.
Definition sort_eqb x y := if S.sort_eq_dec x y then true else false.
Lemma sort_eqb_spec x y : sort_eqb x y = true <-> x=y.
Proof. unfold sort_eqb; destruct (S.sort_eq_dec x y); intuition discriminate. Qed.

(** Program variables, world variables, trace variables and occurrence tags
    occupy distinct syntactic fields. Quantifiers bind named program variables.
    Raw applications have checked argument sorts and arities; quantified bodies have checked
    purity. The rule boundary must require [judgment_wfb]. *)
Inductive term : Type :=
| Var (x : variable)
| Fun (f : S.function_symbol) (args : list term).

Fixpoint term_eq_dec (x y : term) : {x = y} + {x <> y}.
Proof.
  decide equality; try apply variable_eq_dec; try apply S.function_eq_dec.
  apply list_eq_dec; exact term_eq_dec.
Defined.

Definition term_sort (t : term) : S.sort :=
  match t with Var x => fst x | Fun f _ => S.function_result f end.

(** Lists make terms easy to construct. The price is that arity correctness
    is checked explicitly rather than built into the type of [Fun]. *)
Fixpoint term_shapeb (t : term) : bool :=
  match t with
  | Var _ => true
  | Fun f ts => Nat.eqb (length ts) (S.function_arity f) && forallb term_shapeb ts
  end.

Fixpoint term_vars (t : term) : list variable :=
  match t with
  | Var x => [x]
  | Fun _ ts => flat_map term_vars ts
  end.

(** Terms have no binders, so substitution here is a structural traversal.
    Binder capture is handled by the formula substitution operations below. *)
Fixpoint subst_term (x : variable) (replacement t : term) : term :=
  match t with
  | Var y => if variable_eqb x y then replacement else t
  | Fun f ts => Fun f (map (subst_term x replacement) ts)
  end.

(** Formulas mention programs through modalities, while programs mention
    formulas through tests. Mutual definitions and a combined induction
    principle are therefore needed for proofs about the whole language. *)
Inductive formula : Type :=
| Truth
| Pred (p : S.predicate_symbol) (args : list term)
| EqualAt (equality_sort : S.sort) (a b : term)
| Neg (a : formula)
| Conj (a b : formula)
| All (x : variable) (body : formula)
| First (a : formula)
| Suffix (a b : formula)
| Box (p : program) (a : formula)
with program : Type :=
| Assign (x : variable) (value : term)
| Test (guard : formula)
| Seq (a b : program)
| Choice (a b : program)
| Star (body : program).

(** Derived notation expands to primitive syntax. Consequently an abbreviation
    and its expansion have the same equality, substitution and typing behavior. *)
Definition Falsity := Neg Truth.
Definition Disj a b := Neg (Conj (Neg a) (Neg b)).
Definition Impl a b := Neg (Conj a (Neg b)).
Definition Ex x body := Neg (All x (Neg body)).
Definition DualSuffix a b := Neg (Suffix (Neg a) (Neg b)).
Definition Diamond p a := Neg (Box p (Neg a)).

Definition Equal a b := EqualAt (term_sort a) a b.

Scheme formula_mut := Induction for formula Sort Prop
  with program_mut := Induction for program Sort Prop.
Combined Scheme formula_program_mutind from formula_mut, program_mut.

Fixpoint formula_eq_dec (a b : formula) : {a = b} + {a <> b}
with program_eq_dec (a b : program) : {a = b} + {a <> b}.
Proof.
  - decide equality; try apply formula_eq_dec; try apply program_eq_dec;
      try apply term_eq_dec; try apply variable_eq_dec; try apply S.predicate_eq_dec; try apply S.sort_eq_dec.
    apply list_eq_dec; exact term_eq_dec.
  - decide equality; try apply program_eq_dec; try apply formula_eq_dec;
      try apply term_eq_dec; apply variable_eq_dec.
Defined.

(** This single recognizer controls both D2 and the manual pure boundary. *)
Fixpoint pureb (a : formula) : bool :=
  match a with
  | Truth | Pred _ _ | EqualAt _ _ _ => true
  | Neg a | All _ a => pureb a
  | Conj a b => pureb a && pureb b
  | _ => false
  end.

(** The primitive [All] constructor can contain any formula; [Ex] expands to
    a negated universal. This check enforces
    the intended language: their bodies must be recursively pure FOL, as well
    as arity-correct. A modality outside a quantifier remains permitted. *)
Fixpoint formula_shapeb (a : formula) : bool :=
  match a with
  | Truth => true
  | Pred p ts => Nat.eqb (length ts) (S.predicate_arity p) && forallb term_shapeb ts
  | EqualAt equality_sort a b => term_shapeb a && term_shapeb b
  | Neg a | First a => formula_shapeb a
  | Conj a b | Suffix a b =>
      formula_shapeb a && formula_shapeb b
  | All _ a => pureb a && formula_shapeb a
  | Box p a => program_shapeb p && formula_shapeb a
  end
with program_shapeb (p : program) : bool :=
  match p with
  | Assign _ t => term_shapeb t
  | Test a => formula_shapeb a
  | Seq a b | Choice a b => program_shapeb a && program_shapeb b
  | Star a => program_shapeb a
  end.

(** Collect all names, including bound names and assignment targets. This
    deliberately conservative collection is suitable for eigenvariable checks. *)
Fixpoint formula_vars (a : formula) : list variable :=
  match a with
  | Truth => []
  | Pred _ ts => flat_map term_vars ts
  | EqualAt equality_sort a b => term_vars a ++ term_vars b
  | Neg a | First a => formula_vars a
  | Conj a b | Suffix a b =>
      formula_vars a ++ formula_vars b
  | All x a => x :: formula_vars a
  | Box p a => program_vars p ++ formula_vars a
  end
with program_vars (p : program) : list variable :=
  match p with
  | Assign x t => x :: term_vars t
  | Test a => formula_vars a
  | Seq a b | Choice a b => program_vars a ++ program_vars b
  | Star a => program_vars a
  end.

(** Binding-aware substitution on pure syntax. This raw helper stops at a
    binder for [x], but does not rename other binders. [free_forb] supplies a
    sufficient no-capture condition for its semantic correctness theorem.
    Nonpure constructors are left unchanged; this is not an unrestricted
    term-substitution operation for programs or temporal formulas. Public
    quantifier rules use the capture-avoiding [subst_fo] defined below. *)
Fixpoint raw_subst_fo (x : variable) (t : term) (a : formula) : formula :=
  match a with
  | Truth => Truth
  | Pred p ts => Pred p (map (subst_term x t) ts)
  | EqualAt equality_sort l r => EqualAt equality_sort (subst_term x t l) (subst_term x t r)
  | Neg a => Neg (raw_subst_fo x t a)
  | Conj a b => Conj (raw_subst_fo x t a) (raw_subst_fo x t b)
  | All y a => All y (if variable_eqb x y then a else raw_subst_fo x t a)
  | _ => a
  end.

Fixpoint free_forb (x : variable) (t : term) (a : formula) : bool :=
  match a with
  | Truth | Pred _ _ | EqualAt _ _ _ => true
  | Neg a => free_forb x t a
  | Conj a b => free_forb x t a && free_forb x t b
  | All y a =>
      if variable_eqb x y then true
      else negb (existsb (variable_eqb y) (term_vars t)) && free_forb x t a
  | _ => false
  end.

(** Choosing one above the maximum is deterministic and needs no search for
    a witness. Collecting bound names too makes fresh renaming conservative. *)
Definition fresh_name (names : list nat) := Datatypes.S (fold_right Nat.max 0 names).
Lemma fresh_name_not_in names : ~ In (fresh_name names) names.
Proof.
  assert (forall x, In x names -> x <= fold_right Nat.max 0 names) as Hbound.
  { induction names as [|a names IH]; cbn; [tauto|].
    intros x [->|Hin]; [apply Nat.le_max_l|]. eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r]. }
  intro Hin; specialize (Hbound _ Hin); unfold fresh_name in Hbound; lia.
Qed.
Definition fresh_variable (ty : S.sort) (names : list variable) : variable :=
  (ty, fresh_name (map snd names)).
Lemma fresh_variable_not_in ty names : ~ In (fresh_variable ty names) names.
Proof.
  intro H; apply (fresh_name_not_in (map snd names)).
  change (In (snd (fresh_variable ty names)) (map snd names)). now apply in_map.
Qed.
Lemma occursb_false x names : existsb (variable_eqb x) names = false <-> ~ In x names.
Proof.
  rewrite <- not_true_iff_false, existsb_exists. split.
  - intros H Hin; apply H; exists x; split; [exact Hin|apply variable_eqb_refl].
  - intros H [y [Hin Heq]]; apply variable_eqb_eq in Heq; subst; contradiction.
Qed.

(** Renaming a binder changes its body before substitution recurses, so that
    body is not literally a subterm of the original input. A size bound gives
    a terminating fuel implementation; [raw_subst_size] justifies renaming
    without consuming additional formula depth. *)
Fixpoint fol_size (a : formula) : nat :=
  match a with
  | Neg a | All _ a | First a | Box _ a => Datatypes.S (fol_size a)
  | Conj a b | Suffix a b => Datatypes.S (fol_size a + fol_size b)
  | _ => 1
  end.

Lemma raw_subst_size a x t : fol_size (raw_subst_fo x t a) = fol_size a.
Proof.
  induction a; cbn [raw_subst_fo fol_size]; try congruence;
    destruct (variable_eqb x x0); cbn [fol_size]; congruence.
Qed.

Lemma raw_subst_pure a x t : pureb a = true -> pureb (raw_subst_fo x t a) = true.
Proof.
  induction a; cbn [pureb raw_subst_fo]; intro H; try discriminate; try reflexivity;
    try (apply andb_true_iff in H; rewrite IHa1, IHa2 by tauto; reflexivity);
    try (apply IHa; exact H);
    destruct (variable_eqb x x0); cbn [pureb]; auto.
Qed.

Lemma rename_free_for a u v : pureb a = true -> ~ In v (formula_vars a) -> free_forb u (Var v) a = true.
Proof.
  induction a; cbn [pureb free_forb formula_vars]; intros Hp Hv; try discriminate; try reflexivity;
    try (apply IHa; assumption).
  - apply andb_true_iff in Hp as [Ha Hb]; apply andb_true_iff; split;
      [apply IHa1|apply IHa2]; try assumption; intro H; apply Hv; apply in_app_iff; auto.
  - destruct (variable_eqb u x); [reflexivity|]. apply andb_true_iff; split.
    + apply negb_true_iff, occursb_false; cbn [term_vars]; intro H; destruct H; [subst|contradiction]; apply
      Hv; now left.
    + apply IHa; [exact Hp|intro H; apply Hv; now right].
Qed.

(** Total capture-avoiding substitution. At a quantifier there are three
    cases: its binder shadows [x]; its binder would capture a name of [t]; or
    substitution may descend directly. In the second case, rename first to a
    name fresh for the body, replacement and substituted variable. The fuel
    is a proved structural bound; public callers do not choose it. *)
Fixpoint subst_fo_fuel (fuel : nat) (x : variable) (t : term) (a : formula) : formula :=
  match fuel with
  | 0 => a
  | Datatypes.S fuel =>
    match a with
    | Truth => Truth
    | Pred p ts => Pred p (map (subst_term x t) ts)
    | EqualAt equality_sort l r => EqualAt equality_sort (subst_term x t l) (subst_term x t r)
    | Neg a => Neg (subst_fo_fuel fuel x t a)
    | Conj a b => Conj (subst_fo_fuel fuel x t a) (subst_fo_fuel fuel x t b)
    | All y body =>
        if variable_eqb x y then a
        else if existsb (variable_eqb y) (term_vars t) then
          let z := fresh_variable (fst y) (x :: y :: (formula_vars body ++ term_vars t)) in
          All z (subst_fo_fuel fuel x t (raw_subst_fo y (Var z) body))
        else All y (subst_fo_fuel fuel x t body)
    | _ => a
    end
  end.

Definition subst_fo x t a := subst_fo_fuel (fol_size a) x t a.

Lemma subst_fo_fuel_pure fuel : forall x t a, pureb a = true -> pureb (subst_fo_fuel fuel x t a) = true.
Proof.
  induction fuel as [|fuel IH]; intros x t a Hp; [exact Hp|].
  destruct a; cbn [subst_fo_fuel pureb] in *; try discriminate; try reflexivity;
    try (apply IH; exact Hp);
    try (apply andb_true_iff in Hp; rewrite !IH by tauto; reflexivity);
    destruct (variable_eqb x x0); [exact Hp|];
    destruct (existsb (variable_eqb x0) (term_vars t)); cbn [pureb];
    apply IH; try (apply raw_subst_pure); exact Hp.
Qed.

(** These abbreviations inherit finite-trace suffix semantics. In particular
    [Next] is false at the last state; [Always] includes the current state.
    Their semantic boundary laws are proved in Semantics.v. *)
Definition Next a := Suffix Falsity a.
Definition Eventually a := Disj a (Suffix Truth a).
Definition Always a := Neg (Eventually (Neg a)).

(** Reusable transformations contain no world names. State expressions apply
    them to a named state. Parallel RHSs all read the same input state. *)
Inductive update : Type :=
| Skip
| Put (target : variable) (value : term)
| Then (first second : update)
| Parallel (assignments : list (variable * term)).
Fixpoint update_eq_dec (a b : update) : {a=b}+{a<>b}.
Proof.
  decide equality; try apply term_eq_dec; try apply variable_eq_dec.
  apply list_eq_dec; decide equality; [apply term_eq_dec|apply variable_eq_dec].
Defined.
Inductive state_expr : Type :=
| Base (world_variable : nat)
| Apply (transformation : update) (previous : state_expr).
Definition AssignUpdate x t previous := Apply (Put x t) previous.
Fixpoint state_expr_eq_dec (a b : state_expr) : {a=b}+{a<>b}.
Proof. decide equality; try apply update_eq_dec; apply Nat.eq_dec. Defined.

Fixpoint sorts_eqb (a b : list S.sort) :=
  match a,b with
  | [],[] => true
  | x::xs,y::ys => sort_eqb x y && sorts_eqb xs ys
  | _,_ => false end.
Lemma sorts_eqb_spec a b : sorts_eqb a b = true <-> a=b.
Proof.
  revert b; induction a as [|x xs IH]; intros [|y ys]; cbn; try (split; congruence).
  rewrite andb_true_iff, sort_eqb_spec, IH; split; [intros [-> ->]; reflexivity|intro H; inversion H; auto].
Qed.
Fixpoint term_sortedb t : bool :=
  match t with
  | Var _ => true
  | Fun f ts => sorts_eqb (map term_sort ts) (S.function_arguments f) && forallb term_sortedb ts
  end.
Inductive term_sorted : term -> Prop :=
| SortedVar x : term_sorted (Var x)
| SortedFun f ts : map term_sort ts = S.function_arguments f ->
    Forall term_sorted ts -> term_sorted (Fun f ts).
Lemma term_sortedb_spec t : term_sortedb t = true <-> term_sorted t.
Proof.
  revert t; fix IH 1; intros [x|f ts]; cbn [term_sortedb].
  - split; [intro H; constructor|auto].
  - assert (forallb term_sortedb ts = true <-> Forall term_sorted ts) as Hargs.
    { induction ts as [|a rest IHrest]; cbn; [split; constructor|].
      rewrite andb_true_iff, (IH a), IHrest.
      split; [intros [Ha Hr]; constructor; assumption|intro H; inversion H; auto]. }
    rewrite andb_true_iff, sorts_eqb_spec, Hargs.
    split; [intros [Hs Hts]; constructor; assumption|intro H; inversion H; auto].
Qed.
Lemma terms_sortedb_spec ts : forallb term_sortedb ts = true <-> Forall term_sorted ts.
Proof.
  induction ts as [|a rest IH]; cbn; [split; constructor|].
  rewrite andb_true_iff, term_sortedb_spec, IH.
  split; [intros [Ha Hr]; constructor; assumption|intro H; inversion H; auto].
Qed.

Definition term_wfb t := term_shapeb t && term_sortedb t.
Definition assignment_wfb (a : variable * term) :=
  term_wfb (snd a) && sort_eqb (fst (fst a)) (term_sort (snd a)).
Fixpoint update_wfb u :=
  match u with
  | Skip => true
  | Put x t => assignment_wfb (x,t)
  | Then a b => update_wfb a && update_wfb b
  | Parallel assignments => forallb assignment_wfb assignments
  end.
Fixpoint update_vars u : list variable :=
  match u with
  | Skip => []
  | Put x t => x :: term_vars t
  | Then a b => update_vars a ++ update_vars b
  | Parallel assignments => flat_map (fun a => fst a :: term_vars (snd a)) assignments
  end.
Fixpoint update_targets u : list variable :=
  match u with
  | Skip => []
  | Put x _ => [x]
  | Then a b => update_targets a ++ update_targets b
  | Parallel assignments => map fst assignments end.
Fixpoint state_expr_wfb u :=
  match u with Base _ => true | Apply a u => update_wfb a && state_expr_wfb u end.
Fixpoint state_expr_vars u : list variable :=
  match u with Base _ => [] | Apply a u => update_vars a ++ state_expr_vars u end.

Fixpoint formula_sortedb a : bool :=
  match a with
  | Truth => true
  | Pred p ts => sorts_eqb (map term_sort ts) (S.predicate_arguments p) && forallb term_sortedb ts
  | EqualAt ty a b => sort_eqb (term_sort a) ty && sort_eqb (term_sort b) ty && term_sortedb a &&
    term_sortedb b
  | Neg a | First a | All _ a => formula_sortedb a
  | Conj a b | Suffix a b => formula_sortedb a && formula_sortedb b
  | Box p a => program_sortedb p && formula_sortedb a
  end
with program_sortedb p : bool :=
  match p with
  | Assign x t => sort_eqb (fst x) (term_sort t) && term_sortedb t
  | Test a => formula_sortedb a
  | Seq a b | Choice a b => program_sortedb a && program_sortedb b
  | Star a => program_sortedb a
  end.
Fixpoint formula_sorted a : Prop :=
  match a with
  | Truth => True
  | Pred p ts => map term_sort ts = S.predicate_arguments p /\ Forall term_sorted ts
  | EqualAt ty a b => term_sort a = ty /\ term_sort b = ty /\ term_sorted a /\ term_sorted b
  | Neg a | First a | All _ a => formula_sorted a
  | Conj a b | Suffix a b => formula_sorted a /\ formula_sorted b
  | Box p a => program_sorted p /\ formula_sorted a end
with program_sorted p : Prop :=
  match p with
  | Assign x t => fst x = term_sort t /\ term_sorted t
  | Test a => formula_sorted a
  | Seq a b | Choice a b => program_sorted a /\ program_sorted b
  | Star a => program_sorted a end.
Lemma formula_program_sortedb_spec :
  (forall a, formula_sortedb a = true <-> formula_sorted a) /\
  (forall p, program_sortedb p = true <-> program_sorted p).
Proof.
  apply formula_program_mutind; intros; cbn [formula_sortedb program_sortedb formula_sorted program_sorted];
    rewrite ?andb_true_iff, ?sort_eqb_spec, ?sorts_eqb_spec, ?term_sortedb_spec, ?terms_sortedb_spec; tauto.
Qed.
Lemma formula_sortedb_spec a : formula_sortedb a = true <-> formula_sorted a.
Proof. apply formula_program_sortedb_spec. Qed.
Lemma program_sortedb_spec p : program_sortedb p = true <-> program_sorted p.
Proof. apply formula_program_sortedb_spec. Qed.

Definition formula_wfb a := formula_shapeb a && formula_sortedb a.
Definition program_wfb p := program_shapeb p && program_sortedb p.

Inductive label : Type :=
| Empty
| StateLabel (u : state_expr)
| TraceLabel (trace_variable : nat)
| Join (a b : label).
Fixpoint label_eq_dec (a b : label) : {a=b}+{a<>b}.
Proof. decide equality; try apply state_expr_eq_dec; apply Nat.eq_dec. Defined.
Fixpoint label_wfb l :=
  match l with
  | StateLabel u => state_expr_wfb u
  | Join a b => label_wfb a && label_wfb b
  | _ => true end.
Fixpoint label_nonemptyb l :=
  match l with
  | Empty => false
  | StateLabel _ | TraceLabel _ => true
  | Join a b => label_nonemptyb a || label_nonemptyb b end.
Fixpoint label_vars l : list variable :=
  match l with
  | Empty | TraceLabel _ => []
  | StateLabel u => state_expr_vars u
  | Join a b => label_vars a ++ label_vars b end.
Fixpoint subst_world_update (x : nat) (replacement u : state_expr) : state_expr :=
  match u with
  | Base y => if Nat.eqb x y then replacement else u
  | Apply a u => Apply a (subst_world_update x replacement u) end.
Fixpoint subst_world_label (x : nat) (replacement : state_expr) l :=
  match l with
  | StateLabel u => StateLabel (subst_world_update x replacement u)
  | Join a b => Join (subst_world_label x replacement a) (subst_world_label x replacement b)
  | _ => l end.
Fixpoint subst_trace_label (x : nat) (replacement l : label) : label :=
  match l with
  | TraceLabel y => if Nat.eqb x y then replacement else l
  | Join a b => Join (subst_trace_label x replacement a) (subst_trace_label x replacement b)
  | _ => l end.

(** Explicit label algebra, with a caller-selected path: [false] descends
    left, [true] descends right. At the selected node, [left = true] groups
    to the left. An inapplicable path/rotation leaves the relevant syntax
    unchanged. These operations perform no normalization search. *)
Fixpoint rotate_label (path : list bool) (left : bool) (l : label) : label :=
  match path with
  | [] => if left then
      match l with Join a (Join b c) => Join (Join a b) c | _ => l end
    else match l with Join (Join a b) c => Join a (Join b c) | _ => l end
  | direction :: path => match l with
    | Join a b => if direction then Join a (rotate_label path left b)
        else Join (rotate_label path left a) b
    | _ => l end
  end.

(** Use the same paths to insert or remove an explicit [Empty] component.
    Semantics.v proves that both label-algebra operations preserve evaluation. *)
Fixpoint unit_label (path : list bool) (on_left insert : bool) (l : label) : label :=
  match path with
  | [] => if insert then if on_left then Join Empty l else Join l Empty
      else if on_left then match l with Join Empty a => a | _ => l end
      else match l with Join a Empty => a | _ => l end
  | direction :: path => match l with
    | Join a b => if direction then Join a (unit_label path on_left insert b)
        else Join (unit_label path on_left insert a) b
    | _ => l end
  end.

(** Only these succedent formulas can be followed by a cyclic trace. A tag
    identifies an occurrence, not a formula's syntactic position in a list. *)
Definition traceableb (a : formula) : bool :=
  match a with
  | Box _ _ | Suffix _ _ | Neg (Suffix (Neg _) (Neg _)) => true
  | _ => false end.

(** Tags are proof metadata: Semantics.v ignores them when interpreting
    truth, while Progress.v uses them to find the occurrence whose rank is
    followed. Distinct copies of the same labelled formula remain distinct
    occurrences and need distinct tags when both are tagged. *)
Record occurrence : Type := Occ {
  occurrence_label : label;
  occurrence_formula : formula;
  occurrence_tag : option nat
}.

(** [Jdg Gamma Delta] represents a two-sided sequent. Lists preserve exact
    order for graph checking; explicit exchange rules account for reordering.
    Semantically the antecedent is a conjunction and the succedent a
    disjunction, including their empty-list cases. *)
Record judgment : Type := Jdg {
  antecedent : list occurrence;
  succedent : list occurrence
}.

Definition map_label_occurrence (f : label -> label) o :=
  Occ (f o.(occurrence_label)) o.(occurrence_formula) o.(occurrence_tag).
Definition map_labels (f : label -> label) j :=
  Jdg (map (map_label_occurrence f) j.(antecedent)) (map (map_label_occurrence f) j.(succedent)).
Definition rename_occurrence_tag (f : nat -> nat) o :=
  Occ o.(occurrence_label) o.(occurrence_formula) (option_map f o.(occurrence_tag)).
Definition rename_tags (f : nat -> nat) j :=
  Jdg (map (rename_occurrence_tag f) j.(antecedent)) (map (rename_occurrence_tag f) j.(succedent)).

Definition occurrence_eq_dec : forall a b : occurrence, {a = b} + {a <> b}.
Proof.
  decide equality; [decide equality; apply Nat.eq_dec | apply formula_eq_dec | apply label_eq_dec].
Defined.

Definition judgment_eq_dec : forall a b : judgment, {a = b} + {a <> b}.
Proof. decide equality; apply list_eq_dec; apply occurrence_eq_dec. Defined.

Definition judgment_eqb a b := if judgment_eq_dec a b then true else false.
Lemma judgment_eqb_spec a b : judgment_eqb a b = true <-> a = b.
Proof. unfold judgment_eqb; destruct (judgment_eq_dec a b); intuition discriminate. Qed.

(** Exact equality includes tags. Backlink equality ignores only tags:
    labels, update histories, formulas, programs and context order must still
    match. Explicit tag-renaming rules later justify the corresponding ranks. *)
Definition erase_tag o := Occ o.(occurrence_label) o.(occurrence_formula) None.
Definition erase_tags j := Jdg (map erase_tag j.(antecedent)) (map erase_tag j.(succedent)).
Definition backlink_eqb a b := judgment_eqb (erase_tags a) (erase_tags b).

Definition occurrence_vars o := label_vars o.(occurrence_label) ++ formula_vars o.(occurrence_formula).
Definition judgment_vars j := flat_map occurrence_vars (j.(antecedent) ++ j.(succedent)).
Definition eigen_freshb v j l a :=
  negb (existsb (variable_eqb v) (judgment_vars j ++ label_vars l ++ formula_vars a)).

(** The occurrence check combines four independent requirements: valid label
    syntax, nonempty complete label, valid formula syntax, and legal tagging.
    [right] rejects every antecedent tag, even on a box formula. *)
Definition occurrence_wfb (right : bool) o :=
  label_wfb o.(occurrence_label) && label_nonemptyb o.(occurrence_label) &&
  formula_wfb o.(occurrence_formula) &&
  match o.(occurrence_tag) with
  | None => true
  | Some _ => right && traceableb o.(occurrence_formula)
  end.

Definition judgment_tags j :=
  flat_map (fun o => match o.(occurrence_tag) with None => [] | Some n => [n] end)
    j.(succedent).

Fixpoint unique_tagsb (ts : list nat) :=
  match ts with
  | [] => true
  | t :: ts => negb (existsb (Nat.eqb t) ts) && unique_tagsb ts
  end.

(** Uniqueness makes lookup by tag unambiguous. The generic cyclic framework
    checks edge endpoints, but these object-language invariants belong here. *)
Definition judgment_wfb j :=
  forallb (occurrence_wfb false) j.(antecedent) &&
  forallb (occurrence_wfb true) j.(succedent) && unique_tagsb (judgment_tags j).

Lemma unique_tagsb_spec ts : unique_tagsb ts = true <-> NoDup ts.
Proof.
  induction ts as [|t ts IH]; cbn.
  - split; constructor.
  - rewrite andb_true_iff, negb_true_iff, IH.
    assert (existsb (Nat.eqb t) ts = false <-> ~ In t ts) as H.
    { rewrite <- not_true_iff_false, existsb_exists.
      split.
      - intros H Hin. apply H. exists t; split; [exact Hin | apply Nat.eqb_refl].
      - intros H [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst; contradiction. }
    rewrite H. split; [intros [Hn Hd]; constructor; assumption | intro Hd; inversion Hd; auto].
Qed.

Lemma eigen_freshb_spec v j l a :
  eigen_freshb v j l a = true <->
  ~ In v (judgment_vars j ++ label_vars l ++ formula_vars a).
Proof.
  unfold eigen_freshb. rewrite negb_true_iff, <- not_true_iff_false, existsb_exists.
  split.
  - intros H Hin. apply H. exists v; split; [exact Hin | apply variable_eqb_refl].
  - intros H [x [Hin Heq]]. apply variable_eqb_eq in Heq. subst; contradiction.
Qed.

(** Propositional specifications for the executable syntax boundary. In
    particular [pure_formula] is exactly D2's grammar, independently of the
    Boolean recognizer used by generators. *)
Inductive pure_formula : formula -> Prop :=
| PureTruth : pure_formula Truth
| PurePred p ts : pure_formula (Pred p ts)
| PureEqual ty t u : pure_formula (EqualAt ty t u)
| PureNeg a : pure_formula a -> pure_formula (Neg a)
| PureConj a b : pure_formula a -> pure_formula b -> pure_formula (Conj a b)
| PureAll x a : pure_formula a -> pure_formula (All x a).

Definition PureFalsity : pure_formula Falsity := PureNeg Truth PureTruth.
Definition PureDisj a b (Ha : pure_formula a) (Hb : pure_formula b) : pure_formula (Disj a b) :=
  PureNeg _ (PureConj _ _ (PureNeg _ Ha) (PureNeg _ Hb)).
Definition PureImpl a b (Ha : pure_formula a) (Hb : pure_formula b) : pure_formula (Impl a b) :=
  PureNeg _ (PureConj _ _ Ha (PureNeg _ Hb)).
Definition PureEx x a (Ha : pure_formula a) : pure_formula (Ex x a) :=
  PureNeg _ (PureAll _ _ (PureNeg _ Ha)).

Lemma pureb_spec a : pureb a = true <-> pure_formula a.
Proof.
  split.
  - induction a; cbn [pureb]; intro H; try discriminate;
      try solve [constructor]; try solve [constructor; apply IHa; exact H].
    all: apply andb_true_iff in H as [Ha Hb]; constructor;
      [apply IHa1; exact Ha | apply IHa2; exact Hb].
  - intro H; induction H; cbn [pureb];
      rewrite ?IHpure_formula, ?IHpure_formula1, ?IHpure_formula2; reflexivity.
Qed.

Inductive term_shape : term -> Prop :=
| WfVar x : term_shape (Var x)
| WfFun f ts : length ts = S.function_arity f ->
    Forall term_shape ts -> term_shape (Fun f ts).

Lemma term_shapeb_spec t : term_shapeb t = true <-> term_shape t.
Proof.
  revert t; fix IH 1; intro t; destruct t as [x|f ts]; cbn [term_shapeb].
  - split; intro H; [constructor | reflexivity].
  - assert (forallb term_shapeb ts = true <-> Forall term_shape ts) as Hargs.
    { induction ts as [|a ts IHts]; cbn.
      - split; intro H; [constructor | reflexivity].
      - rewrite andb_true_iff, (IH a), IHts.
        split; [intros [Ha Hts]; constructor; assumption | intro H; inversion H; auto]. }
    rewrite andb_true_iff, Nat.eqb_eq, Hargs.
    split; [intros [Harity Hts]; constructor; assumption | intro H; inversion H; auto].
Qed.

Lemma terms_shapeb_spec ts : forallb term_shapeb ts = true <-> Forall term_shape ts.
Proof.
  induction ts as [|t ts IH]; cbn.
  - split; intro H; [constructor | reflexivity].
  - rewrite andb_true_iff, term_shapeb_spec, IH.
    split; [intros [Ht Hts]; constructor; assumption | intro H; inversion H; auto].
Qed.

(** These propositional specifications separate what well-formedness means
    from the executable checks. The mutual reflection proof follows the same
    formula/program induction principle used for semantic freshness later. *)
Fixpoint formula_shape (a : formula) : Prop :=
  match a with
  | Truth => True
  | Pred p ts => length ts = S.predicate_arity p /\ Forall term_shape ts
  | EqualAt equality_sort a b => term_shape a /\ term_shape b
  | Neg a | First a => formula_shape a
  | Conj a b | Suffix a b =>
      formula_shape a /\ formula_shape b
  | All _ a => pure_formula a /\ formula_shape a
  | Box p a => program_shape p /\ formula_shape a
  end
with program_shape (p : program) : Prop :=
  match p with
  | Assign _ t => term_shape t
  | Test a => formula_shape a
  | Seq a b | Choice a b => program_shape a /\ program_shape b
  | Star a => program_shape a
  end.

Lemma formula_program_shapeb_spec :
  (forall a, formula_shapeb a = true <-> formula_shape a) /\
  (forall p, program_shapeb p = true <-> program_shape p).
Proof.
  apply formula_program_mutind; intros; cbn [formula_shapeb program_shapeb formula_shape program_shape];
    rewrite ?andb_true_iff, ?Nat.eqb_eq, ?terms_shapeb_spec, ?term_shapeb_spec,
      ?pureb_spec; intuition.
Qed.

Lemma formula_shapeb_spec a : formula_shapeb a = true <-> formula_shape a.
Proof. apply formula_program_shapeb_spec. Qed.

Lemma program_shapeb_spec p : program_shapeb p = true <-> program_shape p.
Proof. apply formula_program_shapeb_spec. Qed.

Definition term_wf t := term_shape t /\ term_sorted t.
Lemma term_wfb_spec t : term_wfb t = true <-> term_wf t.
Proof. unfold term_wfb, term_wf; rewrite andb_true_iff, term_shapeb_spec, term_sortedb_spec; reflexivity. Qed.

Definition assignment_wf (a : variable * term) := term_wf (snd a) /\ fst (fst a) = term_sort (snd a).
Fixpoint update_wf u : Prop :=
  match u with
  | Skip => True
  | Put x t => assignment_wf (x,t)
  | Then a b => update_wf a /\ update_wf b
  | Parallel assignments => Forall assignment_wf assignments end.
Lemma assignment_wfb_spec a : assignment_wfb a = true <-> assignment_wf a.
Proof. unfold assignment_wfb, assignment_wf; rewrite andb_true_iff, term_wfb_spec, sort_eqb_spec;
  reflexivity. Qed.
Fixpoint state_expr_wf u : Prop :=
  match u with Base _ => True | Apply a u => update_wf a /\ state_expr_wf u end.
Fixpoint label_wf l : Prop :=
  match l with
  | StateLabel u => state_expr_wf u
  | Join a b => label_wf a /\ label_wf b
  | _ => True end.
Lemma update_wfb_spec u : update_wfb u = true <-> update_wf u.
Proof.
  induction u; cbn [update_wfb update_wf]; rewrite ?andb_true_iff, ?assignment_wfb_spec; try tauto.
  rewrite forallb_forall, Forall_forall; setoid_rewrite assignment_wfb_spec; reflexivity.
Qed.
Lemma state_expr_wfb_spec u : state_expr_wfb u = true <-> state_expr_wf u.
Proof. induction u; cbn; [tauto|rewrite andb_true_iff, update_wfb_spec, IHu; reflexivity]. Qed.
Lemma label_wfb_spec l : label_wfb l = true <-> label_wf l.
Proof. induction l; cbn; rewrite ?andb_true_iff, ?state_expr_wfb_spec; tauto. Qed.
Definition formula_wf a := formula_shape a /\ formula_sorted a.
Definition program_wf p := program_shape p /\ program_sorted p.
Lemma formula_wfb_spec a : formula_wfb a = true <-> formula_wf a.
Proof. unfold formula_wfb, formula_wf; rewrite andb_true_iff, formula_shapeb_spec, formula_sortedb_spec;
  reflexivity. Qed.
Lemma program_wfb_spec p : program_wfb p = true <-> program_wf p.
Proof. unfold program_wfb, program_wf; rewrite andb_true_iff, program_shapeb_spec, program_sortedb_spec;
  reflexivity. Qed.

Definition occurrence_wf right o : Prop :=
  label_wf o.(occurrence_label) /\ label_nonemptyb o.(occurrence_label) = true /\
  formula_wf o.(occurrence_formula) /\
  match o.(occurrence_tag) with
  | None => True
  | Some _ => right = true /\ traceableb o.(occurrence_formula) = true
  end.

Definition judgment_wf j : Prop :=
  Forall (occurrence_wf false) j.(antecedent) /\
  Forall (occurrence_wf true) j.(succedent) /\ NoDup (judgment_tags j).

Lemma occurrence_wfb_spec right o : occurrence_wfb right o = true <-> occurrence_wf right o.
Proof.
  unfold occurrence_wfb, occurrence_wf.
  destruct (occurrence_tag o); rewrite !andb_true_iff, label_wfb_spec, formula_wfb_spec;
    intuition.
Qed.

(** This is the full syntax boundary available to a caller who wants to
    reason propositionally after computing [judgment_wfb]. Nonemptiness is
    related to semantic admissibility separately in Semantics.v. *)
Lemma judgment_wfb_spec j : judgment_wfb j = true <-> judgment_wf j.
Proof.
  unfold judgment_wfb, judgment_wf.
  rewrite !andb_true_iff, unique_tagsb_spec, !forallb_forall, !Forall_forall.
  setoid_rewrite occurrence_wfb_spec; tauto.
Qed.

(** Capture avoidance also preserves arities and the recursive pure-body
    invariant. These lemmas require the replacement term to be well formed;
    generators enforce that premise even for an unused replacement. *)
Lemma subst_term_shapeb t : forall x replacement, term_shapeb t = true ->
  term_shapeb replacement = true -> term_shapeb (subst_term x replacement t) = true.
Proof.
  revert t; fix IH 1; intro t; destruct t as [y|f ts]; intros x replacement Ht Hr;
    cbn [subst_term term_shapeb] in *.
  - destruct (variable_eqb x y); assumption.
  - apply andb_true_iff in Ht as [Harity Hargs].
    rewrite length_map, Harity; cbn. clear Harity. revert Hargs.
    induction ts as [|a ts IHts]; cbn; intro Hargs; [reflexivity|].
    apply andb_true_iff in Hargs as [Ha Hts].
    rewrite (IH a x replacement Ha Hr), (IHts Hts); reflexivity.
Qed.

Lemma subst_terms_shapeb ts x t : forallb term_shapeb ts = true -> term_shapeb t = true ->
  forallb term_shapeb (map (subst_term x t) ts) = true.
Proof.
  intros Hts Ht; induction ts as [|a ts IH]; cbn in *; [reflexivity|].
  apply andb_true_iff in Hts as [Ha Hts].
  rewrite subst_term_shapeb by assumption. rewrite IH by assumption. reflexivity.
Qed.

Lemma raw_subst_shapeb a x t : formula_shapeb a = true -> term_shapeb t = true ->
  formula_shapeb (raw_subst_fo x t a) = true.
Proof.
  induction a; cbn [raw_subst_fo formula_shapeb]; intros Ha Ht;
    try exact Ha; try (apply IHa; assumption).
  - apply andb_true_iff in Ha as [Harity Hargs].
    rewrite length_map, Harity, subst_terms_shapeb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr].
    rewrite !subst_term_shapeb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite IHa1, IHa2 by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (variable_eqb x x0); cbn [formula_shapeb].
    + now rewrite Hp, Ha.
    + rewrite raw_subst_pure, IHa by assumption. reflexivity.
Qed.

Lemma subst_fo_fuel_shapeb fuel : forall a x t, formula_shapeb a = true -> term_shapeb t = true ->
  formula_shapeb (subst_fo_fuel fuel x t a) = true.
Proof.
  induction fuel as [|fuel IH]; intros a x t Ha Ht; [exact Ha|].
  destruct a; cbn [subst_fo_fuel formula_shapeb] in *; try exact Ha.
  - apply andb_true_iff in Ha as [Harity Hargs].
    rewrite length_map, Harity, subst_terms_shapeb by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hl Hr].
    rewrite !subst_term_shapeb by assumption. reflexivity.
  - apply IH; assumption.
  - apply andb_true_iff in Ha as [Hl Hr]. rewrite !IH by assumption. reflexivity.
  - apply andb_true_iff in Ha as [Hp Ha]. destruct (variable_eqb x x0); [cbn [formula_shapeb]; now rewrite
    Hp, Ha|].
    destruct (existsb (variable_eqb x0) (term_vars t)); cbn [formula_shapeb];
      rewrite subst_fo_fuel_pure, IH by
        (try apply raw_subst_pure; try apply raw_subst_shapeb; cbn [term_shapeb]; auto);
      reflexivity.
Qed.

Lemma subst_fo_shapeb a x t : formula_shapeb a = true -> term_shapeb t = true ->
  formula_shapeb (subst_fo x t a) = true.
Proof. apply subst_fo_fuel_shapeb. Qed.

Lemma subst_fo_shape a x t : formula_shape a -> term_shape t -> formula_shape (subst_fo x t a).
Proof.
  intros Ha Ht; apply formula_shapeb_spec, subst_fo_shapeb;
    [now apply formula_shapeb_spec | now apply term_shapeb_spec].
Qed.

Lemma subst_fo_pure a x t : pure_formula a -> pure_formula (subst_fo x t a).
Proof. intro Ha; apply pureb_spec, subst_fo_fuel_pure, pureb_spec; exact Ha. Qed.

Lemma subst_world_update_wfb u x replacement : state_expr_wfb u = true ->
  state_expr_wfb replacement = true -> state_expr_wfb (subst_world_update x replacement u) = true.
Proof.
  induction u as [y|a u IH]; cbn [subst_world_update state_expr_wfb]; intros Hu Hr.
  - destruct (Nat.eqb x y); assumption.
  - apply andb_true_iff in Hu as [Ha Hu]. rewrite Ha, IH by assumption; reflexivity.
Qed.
Lemma subst_world_label_wfb l x replacement : label_wfb l = true ->
  state_expr_wfb replacement = true -> label_wfb (subst_world_label x replacement l) = true.
Proof.
  induction l; cbn [subst_world_label label_wfb]; intros Hl Hr; try reflexivity.
  - apply subst_world_update_wfb; assumption.
  - apply andb_true_iff in Hl as [Ha Hb]. rewrite IHl1, IHl2 by assumption; reflexivity.
Qed.
Lemma subst_trace_label_wfb l x replacement : label_wfb l = true ->
  label_wfb replacement = true -> label_wfb (subst_trace_label x replacement l) = true.
Proof.
  induction l as [|u|y|a IHa b IHb]; cbn [subst_trace_label label_wfb]; intros Hl Hr; try exact Hl.
  - destruct (Nat.eqb x y); assumption.
  - apply andb_true_iff in Hl as [Ha Hb]. rewrite IHa, IHb by assumption; reflexivity.
Qed.

(** Sorting is preserved independently of the arity/purity shape proofs.
    The explicit compatibility premise also covers a vacuous binder. *)
Lemma subst_term_sort t x replacement : term_sort replacement = fst x ->
  term_sort (subst_term x replacement t) = term_sort t.
Proof.
  intro Hty; destruct t as [y|f args]; cbn [subst_term term_sort]; [|reflexivity].
  destruct (variable_eqb x y) eqn:H; [apply variable_eqb_eq in H; subst; exact Hty|reflexivity].
Qed.
Lemma subst_term_sortedb t : forall x replacement,
  term_sortedb t = true -> term_sortedb replacement = true -> term_sort replacement = fst x ->
  term_sortedb (subst_term x replacement t) = true.
Proof.
  revert t; fix IH 1; intro t; destruct t as [y|f ts]; intros x replacement Ht Hr Hty;
    cbn [subst_term term_sortedb] in *.
  - destruct (variable_eqb x y); assumption.
  - apply andb_true_iff in Ht as [Hsort Hargs].
    assert (map term_sort (map (subst_term x replacement) ts) = map term_sort ts) as Heq.
    { rewrite map_map; apply map_ext; intro a; apply subst_term_sort; exact Hty. }
    rewrite Heq, Hsort; cbn; clear Hsort Heq.
    induction ts as [|a ts IHts]; cbn in *; [reflexivity|].
    apply andb_true_iff in Hargs as [Ha Hts].
    rewrite (IH a x replacement Ha Hr Hty), IHts by exact Hts; reflexivity.
Qed.
Lemma subst_term_wfb t x replacement : term_wfb t = true -> term_wfb replacement = true ->
  term_sort replacement = fst x -> term_wfb (subst_term x replacement t) = true.
Proof.
  unfold term_wfb; rewrite !andb_true_iff; intros [Ha Hs] [Hra Hrs] Hty; split.
  - now apply subst_term_shapeb.
  - now apply subst_term_sortedb.
Qed.
Lemma subst_terms_sortedb ts x t : forallb term_sortedb ts = true -> term_sortedb t = true ->
  term_sort t = fst x -> forallb term_sortedb (map (subst_term x t) ts) = true.
Proof.
  intros Hts Ht Hty; induction ts as [|a ts IH]; cbn in *; [reflexivity|].
  apply andb_true_iff in Hts as [Ha Hts].
  rewrite subst_term_sortedb, IH by assumption; reflexivity.
Qed.
Lemma subst_term_sorts ts x t : term_sort t = fst x ->
  map term_sort (map (subst_term x t) ts) = map term_sort ts.
Proof. intro Hty; rewrite map_map; apply map_ext; intro a; now apply subst_term_sort. Qed.
Lemma raw_subst_sortedb a x t : formula_sortedb a = true -> term_sortedb t = true ->
  term_sort t = fst x -> formula_sortedb (raw_subst_fo x t a) = true.
Proof.
  induction a; cbn [raw_subst_fo formula_sortedb]; intros Ha Ht Hty;
    try exact Ha; try (apply IHa; assumption).
  - apply andb_true_iff in Ha as [Hs Hargs].
    rewrite subst_term_sorts, subst_terms_sortedb by assumption; now rewrite Hs.
  - repeat rewrite andb_true_iff in Ha; repeat rewrite andb_true_iff; repeat split;
      try (rewrite subst_term_sort by exact Hty; tauto);
      apply subst_term_sortedb; tauto.
  - apply andb_true_iff in Ha as [Hl Hr]; rewrite IHa1, IHa2 by assumption; reflexivity.
  - destruct (variable_eqb x x0); [exact Ha|apply IHa; assumption].
Qed.
Lemma subst_fo_fuel_sortedb fuel : forall a x t,
  formula_sortedb a = true -> term_sortedb t = true -> term_sort t = fst x ->
  formula_sortedb (subst_fo_fuel fuel x t a) = true.
Proof.
  induction fuel as [|fuel IH]; intros a x t Ha Ht Hty; [exact Ha|].
  destruct a; cbn [subst_fo_fuel formula_sortedb] in *; try exact Ha.
  - apply andb_true_iff in Ha as [Hs Hargs].
    rewrite subst_term_sorts, subst_terms_sortedb by assumption; now rewrite Hs.
  - repeat rewrite andb_true_iff in Ha; repeat rewrite andb_true_iff; repeat split;
      try (rewrite subst_term_sort by exact Hty; tauto);
      apply subst_term_sortedb; tauto.
  - apply IH; assumption.
  - apply andb_true_iff in Ha as [Hl Hr]; rewrite !IH by assumption; reflexivity.
  - destruct (variable_eqb x x0); [exact Ha|].
    destruct (existsb (variable_eqb x0) (term_vars t)); apply IH; try assumption.
    apply raw_subst_sortedb; try assumption; reflexivity.
Qed.
Lemma subst_fo_wfb a x t : formula_wfb a = true -> term_wfb t = true ->
  term_sort t = fst x -> formula_wfb (subst_fo x t a) = true.
Proof.
  unfold formula_wfb, term_wfb; rewrite !andb_true_iff.
  intros [Ha Hs] [Ht Hts] Hty; split.
  - now apply subst_fo_shapeb.
  - now apply subst_fo_fuel_sortedb.
Qed.
Lemma subst_fo_wf a x t : formula_wf a -> term_wf t -> term_sort t = fst x ->
  formula_wf (subst_fo x t a).
Proof.
  intros Ha Ht Hty; apply formula_wfb_spec, subst_fo_wfb; try assumption;
    [now apply formula_wfb_spec|now apply term_wfb_spec].
Qed.

(** Explicit, bounded update algebra. A failed path/law is observable as None. *)
Inductive update_law := UpdateSkip | UpdateSequence | UpdateParallelEmpty | UpdateParallelSingleton.
Fixpoint rewrite_state (depth : nat) law u : option state_expr :=
  match depth with
  | 0 => match law,u with
    | UpdateSkip, Apply Skip previous => Some previous
    | UpdateSequence, Apply (Then a b) previous => Some (Apply b (Apply a previous))
    | UpdateParallelEmpty, Apply (Parallel []) previous => Some previous
    | UpdateParallelSingleton, Apply (Parallel [(x,t)]) previous => Some (Apply (Put x t) previous)
    | _,_ => None end
  | Datatypes.S n => match u with
    | Base _ => None
    | Apply a previous => option_map (Apply a) (rewrite_state n law previous) end
  end.
Fixpoint rewrite_update_label (path : list bool) depth law l : option label :=
  match path with
  | [] => match l with
    | StateLabel u => option_map StateLabel (rewrite_state depth law u)
    | _ => None end
  | direction::rest => match l with
    | Join a b => if direction
        then option_map (Join a) (rewrite_update_label rest depth law b)
        else option_map (fun a' => Join a' b) (rewrite_update_label rest depth law a)
    | _ => None end
  end.

End MakeSyntax.
