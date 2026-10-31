(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * Local continuation proofs with actual framework backlinks

    Calls are proof goals, not new LPL program constructors. [approx] is
    used only to interpret a goal at an arbitrary finite observation depth;
    it opens one [unfold_at] layer. Graphs are independent of that depth.
    No state-elimination compiler or separate ASM execution relation is used. *)
From Stdlib Require Import List Bool Arith Lia String Classical_Prop.
From Stdlib Require Import Logic.ClassicalEpsilon.
From CyclistRocq.LPL Require Import Signature Rules.
From CyclistRocq.LPL.ASM Require Import Properties GraphCertification.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module MakeContinuations (S : SIGNATURE) (Kernel : KERNEL S).
Module Export Base := MakeASMProperties S Kernel.

Module Type SPEC.
  Parameter machine : ASM.
  Parameter ends : list (ASM_STATE machine).
  Parameter invariant : state M -> Prop.
  Parameter checked_machine : asm_wfb machine = true.
  Parameter instructions_safe : forall e, In e (transitions machine) ->
    safe invariant (instruction e).
End SPEC.

Module ForSpec (Spec : SPEC).
Import Spec.
Definition endpoint s := exists q, In q ends /\ observed machine q s.
Lemma finish_post q : In q ends -> post endpoint (observe machine q).
Proof. intros Hin tr [s [-> H]]; exists q; auto. Qed.
Definition selected q := existsb (state_eqb machine q) ends.
Lemma selected_spec q : selected q = true <-> In q ends.
Proof.
  unfold selected; rewrite existsb_exists. split.
  - intros [r [Hin Heq]]; apply state_eqb_spec in Heq; now subst.
  - intro Hin; exists q; split; [exact Hin|apply state_eqb_spec; reflexivity].
Qed.
Definition stop q := if selected q then observe machine q else Test Falsity.
Fixpoint approx depth q : program :=
  match depth with
  | 0 => stop q
  | Datatypes.S n =>
      if selected q then Choice (stop q) (unfold_at machine (approx n) q)
      else unfold_at machine (approx n) q
  end.

Lemma unfold_at_checked k q : (forall r, program_wfb (k r) = true) ->
  program_wfb (unfold_at machine k q) = true.
Proof.
  apply unfold_at_wf, checked_machine.
Qed.
Lemma stop_checked q : program_wfb (stop q) = true.
Proof.
  unfold stop; destruct (selected q); [apply observe_wf, checked_machine|reflexivity].
Qed.
Theorem approx_checked depth q : program_wfb (approx depth q) = true.
Proof.
  revert q; induction depth as [|depth IH]; intro q; cbn [approx].
  - apply stop_checked.
  - destruct (selected q); [apply choice_wfb; [apply stop_checked|]|];
      apply unfold_at_checked, IH.
Qed.
Lemma observation_source q s tail : program_holds M (observe machine q) (s::tail) ->
  formula_holds M (state_assertion (description machine q)) [s;s].
Proof. intros [start [Heq H]]; injection Heq as Hs Htail; subst; exact H. Qed.
Lemma unfolding_source k q s tail : program_holds M (unfold_at machine k q) (s::tail) ->
  formula_holds M (state_assertion (description machine q)) [s;s].
Proof.
  apply unfold_at_source_observed.
Qed.
Theorem approx_source_observed depth q s tail :
  program_holds M (approx depth q) (s::tail) ->
  formula_holds M (state_assertion (description machine q)) [s;s].
Proof.
  destruct depth; cbn [approx]; destruct (selected q) eqn:Hsel.
  - unfold stop; rewrite Hsel; apply observation_source.
  - unfold stop; rewrite Hsel; intros [start [Heq Hfalse]]; exfalso; apply Hfalse; exact I.
  - intros [H|H]; [unfold stop in H; rewrite Hsel in H; now apply observation_source in H|].
    now apply unfolding_source in H.
  - apply unfolding_source.
Qed.

(** Finite, nonrecursive proof contexts with named continuation leaves. *)
Inductive fragment :=
| Call (q : ASM_STATE machine)
| Atom (p : program)
| Then (a b : fragment)
| Branch (a b : fragment).
Fixpoint fragment_eq_dec (a b : fragment) : {a=b}+{a<>b}.
Proof. decide equality; [apply (state_eq_dec machine)|apply program_eq_dec]. Defined.
Fixpoint plug (k : ASM_STATE machine -> program) f :=
  match f with Call q => k q | Atom p => p
  | Then a b => Seq (plug k a) (plug k b)
  | Branch a b => Choice (plug k a) (plug k b) end.
Definition join_frag a b := match a,b with
  | None,_ => b | _,None => a | Some p,Some q => Some (Branch p q) end.
Definition frag_code p := match p with None => Atom (Test Falsity) | Some p => p end.
Fixpoint outgoing q es : option fragment :=
  match es with [] => None | e::rest =>
    join_frag (if state_eqb machine q (source e)
      then Some (Then (Atom (instruction e)) (Call (target e))) else None)
      (outgoing q rest) end.
Definition layer q := Then (Atom (observe machine q))
  (frag_code (outgoing q (transitions machine))).
Definition expansion q := if selected q
  then Branch (Atom (stop q)) (layer q) else layer q.
Definition plug_option k p := match p with None => None | Some f => Some (plug k f) end.
Lemma plug_join k a b : plug_option k (join_frag a b) =
  alternative (plug_option k a) (plug_option k b).
Proof. destruct a,b; reflexivity. Qed.
Lemma plug_outgoing k q es : plug_option k (outgoing q es) =
  alternatives (map (fun e => if state_eqb machine q (source e)
    then Some (Seq (instruction e) (k (target e))) else None) es).
Proof.
  induction es as [|e es IH]; cbn [outgoing map alternatives]; [reflexivity|].
  rewrite plug_join, IH. destruct (state_eqb machine q (source e)); reflexivity.
Qed.
Lemma plug_layer k q : plug k (layer q) = unfold_at machine k q.
Proof.
  unfold layer, unfold_at; cbn [plug]. f_equal.
  rewrite <- plug_outgoing. destruct (outgoing q (transitions machine)); reflexivity.
Qed.
Lemma plug_expansion n q : plug (approx n) (expansion q) = approx (Datatypes.S n) q.
Proof. unfold expansion; cbn [approx]; destruct (selected q); cbn [plug]; now rewrite plug_layer. Qed.

Inductive mode := Safety | Contract.
Definition mode_eq_dec : forall a b : mode, {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition good md tr := match md with Safety => Forall invariant tr
  | Contract => Forall invariant tr /\ endpoint (last tr default_state) end.
Definition bad md p tr := program_holds M p tr /\
  exists s tail, tr=s::tail /\ invariant s /\ ~ good md tr.
Definition task := (mode * fragment)%type.
Definition task_eq_dec : forall a b : task, {a=b}+{a<>b}.
Proof. decide equality; [apply fragment_eq_dec|apply mode_eq_dec]. Defined.
Definition task_eqb a b := if task_eq_dec a b then true else false.
Lemma task_eqb_spec a b : task_eqb a b = true <-> a=b.
Proof. unfold task_eqb; destruct (task_eq_dec a b); intuition discriminate. Qed.
Definition world := (nat * list (state M))%type.
Definition task_bad (j : task) (w : world) :=
  bad (fst j) (plug (approx (fst w)) (snd j)) (snd w).

Lemma join_good md a b tr : overlap M a b tr -> Forall invariant a ->
  good md b -> good md tr.
Proof.
  intros Ho Ha Hb.
  assert (forall P, Forall P a -> Forall P b -> Forall P tr) as Hall.
  { intros P Hpa Hpb. destruct Ho as [prefix [s [tail [-> [-> ->]]]]].
    rewrite Forall_app in Hpa |- *; tauto. }
  destruct md; cbn [good] in *; [now apply Hall|].
  destruct Hb as [Hb Hp]; split; [now apply Hall|].
  now rewrite (overlap_list_last _ _ _ default_state Ho).
Qed.
Lemma bad_sequence md p q tr : bad md (Seq p q) tr ->
  (exists a, bad Safety p a) \/ (exists b, bad md q b).
Proof.
  intros [[a [b [Ha [Hb Ho]]]] [s [tail [Htr [Hs Hbad]]]]]; subst tr.
  destruct (overlap_list_head _ _ _ Ho) as [head [arest [ct [Hfirst Hout]]]].
  injection Hout as Hhead Htail; subst head a.
  destruct (classic (Forall invariant (s::arest))) as [Hsafe|Hunsafe].
  - right. exists b; split; [exact Hb|].
    destruct Ho as [prefix [middle [bt [Hend [Hstart Hresult]]]]].
    exists middle,bt; split; [exact Hstart|]. split.
    + rewrite Forall_forall in Hsafe; apply Hsafe. rewrite Hend; apply in_app_iff; cbn; auto.
    + intro Hgood; apply Hbad. eapply join_good; [|exact Hsafe|exact Hgood].
      exists prefix,middle,bt; auto.
  - left. exists (s::arest); split; [exact Ha|]. exists s,arest; auto.
Qed.
Lemma bad_choice md p q tr : bad md (Choice p q) tr -> bad md p tr \/ bad md q tr.
Proof. intros [[H|H] Hbad]; [left|right]; split; assumption. Qed.
Lemma safe_not_bad md p tr : safe invariant p ->
  (md=Contract -> post endpoint p) -> ~ bad md p tr.
Proof.
  intros Hsafe Hpost [Hp [s [tail [-> [Hs Hbad]]]]]. apply Hbad.
  destruct md; cbn [good]; [eapply Hsafe; eauto|].
  split; [eapply Hsafe; eauto|apply (Hpost eq_refl); exact Hp].
Qed.
Lemma false_post : post endpoint (Test Falsity).
Proof. intros tr [s [Heq Hfalse]]; exfalso; apply Hfalse; exact I. Qed.
Lemma stop_safe q : safe invariant (stop q).
Proof. unfold stop; destruct (selected q); apply test_safe. Qed.
Lemma stop_post q : post endpoint (stop q).
Proof.
  unfold stop; destruct (selected q) eqn:H; [apply finish_post; now apply selected_spec|apply false_post].
Qed.
Lemma stop_not_bad md q tr : ~ bad md (stop q) tr.
Proof. apply safe_not_bad; [apply stop_safe|intro; apply stop_post]. Qed.

Module Theory <: CHECKABLE_THEORY.
  Definition World := world.
  Definition Judgment := task.
  Definition Sequent := World -> Prop.
  Definition judgment_eqb := task_eqb.
  Definition backlink_eqb := task_eqb.
  Definition denote j w := ~ task_bad j w.
  Definition tags (_ : Judgment) := [0%nat].
  Definition rank (_ : Judgment) (w : World) (_ : nat) := fst w.
  Definition judgment_eqb_spec := task_eqb_spec.
End Theory.
Module Certification := MakeGraphCertification Theory.
Module Graph := Certification.Cyclic.

(** A rule's backward theorem must provide a genuinely false successor;
    the generic constructor cannot certify an arbitrary graph. *)
Definition edge (progress : bool) : Graph.edge_info :=
  {| Graph.edge_valid := [(0%nat,0%nat)];
     Graph.edge_progress := if progress then [(0%nat,0%nat)] else [] |}.
Definition premise progress j : Graph.premise :=
  {| Graph.premise_judgment := j; Graph.premise_edge := edge progress |}.
Definition step_bound (progress : bool) (w w' : world) :=
  if progress then fst w' < fst w else fst w' <= fst w.
Lemma respects progress j j' w w' : step_bound progress w w' ->
  Graph.respects_edge j j' w w' (edge progress).
Proof.
  unfold step_bound, Graph.respects_edge, edge, Theory.rank.
  destruct progress; cbn; intros H; split; intros a b Hin;
    try contradiction; destruct Hin as [Heq|[]]; inversion Heq; subst; lia.
Qed.
Definition local_rule (name : string) (progress : bool) (j : task) (js : list task)
    (back : forall w, task_bad j w -> exists k w' j',
      nth_error js k=Some j' /\ task_bad j' w' /\ step_bound progress w w') : Graph.rule_instance.
Proof.
  refine {| Graph.rule_name := name; Graph.rule_conclusion := j;
    Graph.rule_premises := map (premise progress) js |}.
  - intros Hvalid w Hbad.
    destruct (back w Hbad) as [k [w' [j' [Hnth [Hbad' Hbound]]]]].
    assert (In (premise progress j') (map (premise progress) js)) as Hin.
    { apply in_map; now apply nth_error_In in Hnth. }
    exact (Hvalid (premise progress j') Hin w' Hbad').
  - intros w Hfalse.
    assert (task_bad j w) as Hbad by (apply NNPP; exact Hfalse).
    assert (exists chosen : nat * world * task,
      let '(k,w',j') := chosen in nth_error js k=Some j' /\
        task_bad j' w' /\ step_bound progress w w') as Hex.
    { destruct (back w Hbad) as [k [w' [j' H]]]; exists (k,w',j'); exact H. }
    destruct (constructive_indefinite_description _ Hex) as [[[k w'] j'] [Hnth [Hbad' Hbound]]].
    exists k, (premise progress j'), w'. split.
    + change (nth_error (map (premise progress) js) k = Some (premise progress j')).
      exact (eq_trans (List.nth_error_map (premise progress) k js)
        (f_equal (option_map (premise progress)) Hnth)).
    + split; [intro Hvalid; exact (Hvalid Hbad')|now apply respects].
Defined.
Definition sequence_rule (md : mode) (a b : fragment) : Graph.rule_instance.
Proof.
  refine (local_rule "LPL.sequence" false (md,Then a b) [(Safety,a);(md,b)] _).
  intros [n tr] H; cbn [task_bad fst snd plug] in H.
  destruct (bad_sequence md _ _ _ H) as [[left_trace Hl]|[right_trace Hr]].
  - exists 0%nat,(n,left_trace),(Safety,a); split; [reflexivity|].
    split; [exact Hl|unfold step_bound; cbn; lia].
  - exists 1%nat,(n,right_trace),(md,b); split; [reflexivity|].
    split; [exact Hr|unfold step_bound; cbn; lia].
Defined.
Definition choice_rule (md : mode) (a b : fragment) : Graph.rule_instance.
Proof.
  refine (local_rule "LPL.choice" false (md,Branch a b) [(md,a);(md,b)] _).
  intros [n tr] H; cbn [task_bad fst snd plug] in H.
  destruct (bad_choice md _ _ _ H) as [Hl|Hr].
  - exists 0%nat,(n,tr),(md,a); split; [reflexivity|].
    split; [exact Hl|unfold step_bound; cbn; lia].
  - exists 1%nat,(n,tr),(md,b); split; [reflexivity|].
    split; [exact Hr|unfold step_bound; cbn; lia].
Defined.
Definition unfold_rule (md : mode) (q : ASM_STATE machine) : Graph.rule_instance.
Proof.
  refine (local_rule "ASM.unfold_at" true (md,Call q) [(md,expansion q)] _).
  intros [[|n] tr] H.
  - exfalso; exact (stop_not_bad md q tr H).
  - exists 0%nat,(n,tr),(md,expansion q); split; [reflexivity|]. split; [|cbn; lia].
    unfold task_bad; cbn. rewrite plug_expansion; exact H.
Defined.
Definition backlink_rule (j : task) : Graph.rule_instance.
Proof.
  refine (local_rule "ASM.backlink.exact" false j [j] _).
  intros w H; exists 0%nat,w,j; split; [reflexivity|].
  split; [exact H|unfold step_bound; lia].
Defined.

Definition program_eqb p q := if program_eq_dec p q then true else false.
Lemma program_eqb_spec p q : program_eqb p q = true <-> p=q.
Proof. unfold program_eqb; destruct (program_eq_dec p q); intuition discriminate. Qed.
Definition safe_atoms := map instruction (transitions machine) ++
  map (observe machine) (states machine) ++ [Test Falsity].
Definition post_atoms := map (observe machine) ends ++ [Test Falsity].
Definition member_program p ps := existsb (program_eqb p) ps.
Lemma member_program_spec p ps : member_program p ps = true <-> In p ps.
Proof.
  unfold member_program; rewrite existsb_exists. split.
  - intros [q [Hin Heq]]; apply program_eqb_spec in Heq; now subst.
  - intro Hin; exists p; split; [exact Hin|apply program_eqb_spec; reflexivity].
Qed.
Lemma safe_atom p : member_program p safe_atoms = true -> safe invariant p.
Proof.
  rewrite member_program_spec; unfold safe_atoms; rewrite !in_app_iff.
  intros [H|[H|[<-|[]]]]; [| |apply test_safe].
  - apply in_map_iff in H as [e [<- Hin]]; now apply instructions_safe.
  - apply in_map_iff in H as [q [<- Hin]]; apply test_safe.
Qed.
Lemma post_atom p : member_program p post_atoms = true -> post endpoint p.
Proof.
  rewrite member_program_spec; unfold post_atoms; rewrite in_app_iff.
  intros [H|[<-|[]]]; [|apply false_post].
  apply in_map_iff in H as [q [<- Hin]]; now apply finish_post.
Qed.
Definition leafb md p := program_wfb p && member_program p safe_atoms &&
  match md with Safety => true | Contract => member_program p post_atoms end.
Definition leaf_axiom md p (H : leafb md p = true) : Graph.axiom_instance.
Proof.
  refine {| Graph.axiom_name := "LPL.local_instruction"; Graph.axiom_conclusion := (md,Atom p) |}.
  intros [n tr]; apply safe_not_bad.
  - apply safe_atom. unfold leafb in H; apply andb_true_iff in H as [H _].
    now apply andb_true_iff in H as [_ H].
  - intro Hmd; cbn in Hmd; subst md; apply post_atom.
    unfold leafb in H; now apply andb_true_iff in H as [_ H].
Defined.
Definition checked_leaf (md : mode) (p : program) : option Graph.axiom_instance.
Proof. destruct (leafb md p) eqn:H; [exact (Some (leaf_axiom md p H))|exact None]. Defined.

(** Work-list proof construction: only Call goals are memoized. An actual
    AddBacklink command closes a repeated call; no recursion is guessed. *)
Fixpoint companion j (seen : list (task * nat)) := match seen with [] => None | (k,i)::rest =>
  if task_eqb j k then Some i else companion j rest end.
Fixpoint build_work fuel todo seen st : Graph.build_state :=
  match fuel,todo with
  | 0,_ => st | _,[] => st
  | Datatypes.S fuel,(i,(md,f))::rest =>
      match f with
      | Atom p => match checked_leaf md p with
        | None => st
        | Some ax => build_work fuel rest seen (Graph.execute st (Graph.CloseWith i ax)) end
      | Call q => match companion (md,f) seen with
        | Some target => build_work fuel rest seen
            (Graph.execute st (Graph.AddBacklink i target (backlink_rule (md,f))))
        | None => let next := List.length (Graph.graph_nodes (Graph.built_graph st)) in
            build_work fuel ((next,(md,expansion q))::rest) (((md,f),i)::seen)
              (Graph.execute st (Graph.ApplyRule i (unfold_rule md q))) end
      | Then a b => let next := List.length (Graph.graph_nodes (Graph.built_graph st)) in
          build_work fuel ((next,(Safety,a))::(Datatypes.S next,(md,b))::rest) seen
            (Graph.execute st (Graph.ApplyRule i (sequence_rule md a b)))
      | Branch a b => let next := List.length (Graph.graph_nodes (Graph.built_graph st)) in
          build_work fuel ((next,(md,a))::(Datatypes.S next,(md,b))::rest) seen
            (Graph.execute st (Graph.ApplyRule i (choice_rule md a b)))
      end
  end.
Definition build fuel md q := build_work fuel [(0%nat,(md,Call q))] []
  (Graph.begin_build (md,Call q)).
Fixpoint fragment_size f := match f with Call _ | Atom _ => 1%nat
  | Then a b | Branch a b => Datatypes.S (fragment_size a + fragment_size b) end.
Definition witness (g : Graph.graph) : Graph.trace_witness :=
  {| Graph.witness_tag := fun _ => Some 0%nat;
     Graph.witness_potential := fun i => match Graph.node_at g i with
       | None => 0%nat | Some n => match Graph.node_payload n with
         | Graph.BacklinkNode _ _ => 1%nat
         | _ => match snd (Graph.node_judgment n) with
           | Call _ => 0%nat | f => fragment_size f + 2 end end end |}.
Definition backlink_count g := List.length (filter (fun n => match Graph.node_payload n with
  Graph.BacklinkNode _ _ => true | _ => false end) (Graph.graph_nodes g)).

Theorem accepted_safe g q : Graph.graph_root g = (Contract,Call q) ->
  Graph.raw_check g (witness g) = true -> forall depth, safe invariant (approx depth q).
Proof.
  intros Hroot Hcheck depth s tail Hrun Hinv.
  pose proof (Certification.raw_check_sound g (witness g) Hcheck (depth,s::tail)) as Hvalid.
  rewrite Hroot in Hvalid. apply NNPP; intro Hbad. apply Hvalid.
  split; [exact Hrun|]. exists s,tail; split; [reflexivity|]. split; [exact Hinv|].
  intros [Hgood _]; contradiction.
Qed.
Theorem accepted_post g q : Graph.graph_root g = (Contract,Call q) ->
  Graph.raw_check g (witness g) = true -> forall depth s tail,
  program_holds M (approx depth q) (s::tail) -> invariant s -> endpoint (last (s::tail) default_state).
Proof.
  intros Hroot Hcheck depth s tail Hrun Hinv.
  pose proof (Certification.raw_check_sound g (witness g) Hcheck (depth,s::tail)) as Hvalid.
  rewrite Hroot in Hvalid. apply NNPP; intro Hbad. apply Hvalid.
  split; [exact Hrun|]. exists s,tail; split; [reflexivity|]. split; [exact Hinv|].
  intros [_ Hgood]; contradiction.
Qed.

End ForSpec.
End MakeContinuations.
