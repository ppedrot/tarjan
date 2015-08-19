Require FSets FMaps NArith Wellfounded.
Require Import Program Setoid Morphisms BinNat Relations.

Obligation Tactic := idtac.
Set Primitive Projections.

Axiom admit : False.
Ltac admit := exfalso; exact admit.

Module Univ
  (Level : OrderedType.OrderedType)
  (UMap : FMapInterface.Sfun(Level))
  (USet : FSetInterface.Sfun(Level))
.

Module Import USetFacts := FSetFacts.WFacts_fun(Level)(USet).
Module Import UMapFacts := FMapFacts.WProperties_fun(Level)(UMap).

Inductive status := NoMark | Visited | WeakVisited | ToMerge.

Record canonical_node :=
{ univ: Level.t;
  ltle: UMap.t bool;
  gtge: USet.t;
  rank : N;
(*   predicative : bool; *)
  klvl: N;
  ilvl: N
}.

Definition order u v :=
match (u.(klvl) ?= v.(klvl))%N with
| Lt => Lt
| Gt => Gt
| Eq => (u.(ilvl) ?= v.(ilvl))%N
end.

Definition big_rank : N := 10000.

(* A Level.t is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)

Inductive univ_entry :=
| Canonical : canonical_node -> univ_entry
| Equiv : Level.t -> univ_entry.

Record universes :=
  { entries : UMap.t univ_entry;
    index : N;
    n_nodes : N; n_edges : N }.

Inductive ueq_step g (u : Level.t) (v : Level.t) : Prop :=
| ueq_step_eq : forall w,
  Level.eq v w ->
  UMap.MapsTo u (Equiv w) g ->
  ueq_step g u v.

Inductive ule_step g (u : Level.t) (v : Level.t) : Prop :=
| ule_step_le : forall n,
  UMap.MapsTo u (Canonical n) g ->
  UMap.MapsTo v false n.(ltle) ->
  ule_step g u v
| ule_step_eq : forall w,
  Level.eq v w ->
  UMap.MapsTo u (Equiv w) g ->
  ule_step g u v.

Inductive ult_step g (u : Level.t) (v : Level.t) : Prop :=
| ult_step_lt : forall n,
  UMap.MapsTo u (Canonical n) g ->
  UMap.In v n.(ltle) ->
  ult_step g u v
| ult_step_eq : forall w,
  Level.eq v w ->
  UMap.MapsTo u (Equiv w) g ->
  ult_step g u v.

Inductive is_canonical g u : Prop :=
| canonical_intro : forall n,
  Level.eq u n.(univ) ->
  UMap.MapsTo u (Canonical n) g ->
  is_canonical g u.

Instance Proper_ueq_step : forall g, Proper (Level.eq ==> Level.eq ==> iff) (ueq_step g).
Proof.
intros g; eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros u1 u2 Hu v1 v2 Hv Hrw.
destruct Hrw.
+ rewrite Hu, Hv in *; eapply ueq_step_eq; eassumption.
Qed.

Instance Proper_ule_step : forall g, Proper (Level.eq ==> Level.eq ==> iff) (ule_step g).
Proof.
intros g; eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros u1 u2 Hu v1 v2 Hv Hrw.
destruct Hrw.
+ rewrite Hu, Hv in *; eapply ule_step_le; eassumption.
+ rewrite Hu, Hv in *; eapply ule_step_eq; eassumption.
Qed.

Instance Proper_ult_step : forall g, Proper (Level.eq ==> Level.eq ==> iff) (ult_step g).
Proof.
intros g; eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros u1 u2 Hu v1 v2 Hv Hrw.
destruct Hrw.
+ rewrite Hu, Hv in *; eapply ult_step_lt; eassumption.
+ rewrite Hu, Hv in *; eapply ult_step_eq; eassumption.
Qed.

Instance Proper_is_canonical : forall g, Proper (Level.eq ==> iff) (is_canonical g).
Proof.
intros g; eapply proper_sym_impl_iff; [now eauto|].
intros u1 u2 Hu Hrw; destruct Hrw.
rewrite Hu in *; econstructor; eassumption.
Qed.

Instance Proper_clos_trans : forall A (R eq : relation A),
  Equivalence eq ->
  Proper (eq ==> eq ==> iff) R ->
  Proper (eq ==> eq ==> iff) (clos_trans _ R).
Proof.
intros A R eq Heq HR.
eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros x1 x2 Hx y1 y2 Hy Hr.
revert x2 Hx y2 Hy; induction Hr; intros x2 Hx y2 Hy.
+ apply t_step; compute in Hx.
  rewrite <- Hx, <- Hy; assumption.
+ eapply t_trans; [eapply IHHr1|eapply IHHr2]; (eassumption || reflexivity).
Qed.

Module Rel.

Definition eq g (u v : Level.t) :=
  clos_refl_sym_trans _ (relation_disjunction (ueq_step g) Level.eq) u v.

Instance Equivalence_eq : forall g, Equivalence (eq g).
Proof.
intros g.
destruct (clos_rst_is_equiv _ (relation_disjunction (ueq_step g) Level.eq)); split.
+ apply equiv_refl.
+ apply equiv_sym.
+ apply equiv_trans.
Qed.

Instance subrelation_eq : forall g, subrelation Level.eq (eq g).
Proof.
intros g u v H; apply rst_step; right; assumption.
Qed.

End Rel.

Existing Instance Rel.Equivalence_eq.

Lemma eq_alt_iff : forall g u v,
  Rel.eq g u v <-> (Level.eq u v \/ clos_refl_sym_trans _ (ueq_step g) u v).
Proof.
intros g u v; split; intros Hr.
+ apply clos_rst_rst1n_iff in Hr; induction Hr as [u|u v w [H|H] Hr [IH|IH]].
  - left; reflexivity.
  - destruct H; rewrite IH in H; [right; apply rst_step|left]; intuition.
  - destruct H.
    { right; eapply rst_trans; [|eassumption].
      apply rst_step; intuition. }
    { apply clos_rst_rst1n_iff in IH; clear - IH H.
      revert u H; induction IH as [|v w z Hr _ IH]; [intuition|intros u H; right].
      rewrite <- H in Hr; clear v H.
      specialize (IH w); destruct IH; [reflexivity| |].
      + rewrite H in Hr; clear H; apply clos_rst_rst1n_iff; eright; [eauto|apply rst1n_refl].
      + apply clos_rst_rst1n_iff; eright; [|apply clos_rst_rst1n_iff]; eassumption.
    }
  - destruct H.
    { rewrite IH in H; right; apply rst_sym, rst_step; assumption. }
    { left; rewrite <- H, IH; reflexivity. }
  - destruct H.
    { right; eapply rst_trans; [|eassumption]; eapply rst_sym, rst_step, H. }
    { apply clos_rst_rst1n_iff in IH; clear - IH H; symmetry in H.
      revert u H; induction IH as [|v w z Hr _ IH]; [intuition|intros u H; right].
      rewrite <- H in Hr; clear v H.
      specialize (IH w); destruct IH; [reflexivity| |].
      + rewrite H in Hr; clear H; apply clos_rst_rst1n_iff; eright; [eauto|apply rst1n_refl].
      + apply clos_rst_rst1n_iff; eright; [|apply clos_rst_rst1n_iff]; eassumption.
    }
+ destruct Hr as [Hr|Hr].
  - rewrite Hr; reflexivity.
  - apply clos_rst_rst1n_iff in Hr; induction Hr as [u|u v w [H|H] Hr IH].
    { reflexivity. }
    { transitivity v; [|assumption]; apply rst_step; left; assumption. }
    { transitivity v; [|assumption]; symmetry; apply rst_step; left; assumption. }
Qed.

Record Repr g u n : Prop :=  {
  Repr_wit : Level.t;
  Repr_rel : Rel.eq g u Repr_wit;
  Repr_can : UMap.MapsTo Repr_wit (Canonical n) g
}.

Instance Proper_Repr : forall g, Proper (Level.eq ==> eq ==> iff) (Repr g).
Proof.
intros g; eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros u1 u2 Hu n1 n2 Hn Hrw; rewrite <- Hn; clear n2 Hn; rename n1 into n.
destruct Hrw as [v Hl Hr]; exists v.
+ clear - Hl Hu; apply eq_alt_iff in Hl.
  destruct Hl as [Hl|Hl]; [rewrite <- Hu, Hl; reflexivity|].
  apply clos_rst_rst1n_iff in Hl; revert u2 Hu.
  induction Hl as [|u w v [H|H] Hl IH]; intros u2 Hu.
  - rewrite Hu; reflexivity.
  - rewrite Hu in *; clear u Hu.
    transitivity w; [|eapply IH; reflexivity].
    apply rst_step; left; assumption.
  - rewrite Hu in *; clear u Hu.
    transitivity w; [|eapply IH; reflexivity].
    symmetry; apply rst_step; left; assumption.
+ assumption.
Qed.

Record Universes := {
  ugraph :> universes;
  ult_trans_wf :
    well_founded (Basics.flip (ult_step ugraph.(entries)));
  ult_complete : forall u v,
    ult_step ugraph.(entries) u v -> UMap.In v ugraph.(entries);
  ueq_canonical : forall u n,
    UMap.MapsTo u (Canonical n) ugraph.(entries) -> Level.eq u n.(univ);
  unv_topo_rel : forall u v m n,
    UMap.MapsTo u (Canonical m) ugraph.(entries) ->
    UMap.In v m.(ltle) ->
    Repr ugraph.(entries) v n -> order m n = Lt

(* ; *)
(*   unv_gtge_rev : forall u v m n, *)
(*     UMap.MapsTo u (Canonical n) ugraph.(entries) -> *)
(*     UMap.In v n.(ltle) -> Repr ugraph.(entries) v m -> n.(klvl) = m.(klvl) -> *)
(*     exists p, USet.In p.(univ) m.(gtge) /\ Repr ugraph.(entries) u p *)
}.

(*
Lemma deterministic_clos_trans_1n :
  forall A (R eq : relation A) x y z,
  Equivalence eq ->
  Proper (eq ==> eq ==> iff) R ->
  Proper (R ==> R ==> Basics.impl) eq ->
  clos_trans _ R x z -> R x y -> eq y z \/ clos_trans _ R y z.
Proof.
intros A R eq x y z Heq Hp Hdet Hct Hr.
apply clos_trans_tn1_iff in Hct.
revert y Hr; induction Hct as [z Hr|z y Hr Hct IH]; intros a Ha.
+ left.
  eapply Hdet; try eassumption; reflexivity.
+ specialize (IH a Ha); destruct IH as [IH|IH].
  - rewrite <- IH in Hr.
    right; apply t_step; assumption.
  - right; eapply t_trans; [eassumption|].
    apply t_step; eassumption.
Qed.

Instance deterministic_ueq_r : forall g,
  Proper (ueq_step g ==> ueq_step g ==> Basics.impl) Level.eq.
Proof.
intros g u1 u2 Hu v1 v2 Hv Hrw.
rewrite <- Hrw in *; clear v1 Hrw; rename v2 into v.
destruct Hu as [w1 Hw1 Hu], Hv as [w2 Hw2 Hv].
rewrite Hw1 in *; rewrite Hw2 in *; clear u2 v Hw1 Hw2.
apply UMap.find_1 in Hu.
apply UMap.find_1 in Hv.
replace w1 with w2 by congruence; reflexivity.
Qed.

Instance deterministic_ueq_l : forall g,
  Proper (Basics.flip (ueq_step g) ==> Basics.flip (ueq_step g) ==> Basics.impl) Level.eq.
Proof.
intros g u1 u2 Hu v1 v2 Hv Hrw.
rewrite <- Hrw in *; clear v1 Hrw; rename v2 into v.
destruct Hu as [w1 Hw1 Hu], Hv as [w2 Hw2 Hv].
rewrite Hw1 in *; clear u1 Hw1.

apply UMap.find_1 in Hu.
apply UMap.find_1 in Hv.
replace w1 with w2 by congruence; reflexivity.
Qed.


Inductive trichotomy {A} (eq lt : relation A) (x y : A) : Prop :=
| trichotomy_eq : eq x y -> trichotomy eq lt x y
| trichotomy_lt : lt x y -> trichotomy eq lt x y
| trichotomy_gt : lt y x -> trichotomy eq lt x y.

Lemma ueq_step_trichotomy : forall (g : Universes) u v,
  Rel.eq g.(entries) u v -> trichotomy Level.eq (clos_trans _ (ueq_step g.(entries))) u v.
Proof.
intros g u v Hr.
apply clos_rst_rst1n_iff in Hr; induction Hr as [u|u v w [[H|H]|[H|H]] Hr IH].
+ apply trichotomy_eq; reflexivity.
+ destruct IH as [Hrw|Hlt|Hgt].
  - apply trichotomy_lt, t_step; rewrite <- Hrw; assumption.
  - apply trichotomy_lt; eapply t_trans; [|eassumption]; eapply t_step; assumption.
  -

*)

Lemma is_canonical_minimal : forall g u v,
  is_canonical g u -> ~ ueq_step g u v.
Proof.
intros g u v Hu Hs.
destruct Hs as [w Hrw Hw].
destruct Hu as [n Hn Hu].
apply UMap.find_1 in Hw; apply UMap.find_1 in Hu; congruence.
Qed.

Lemma is_canonical_rt : forall (g : Universes) u v,
  Rel.eq g.(entries) u v -> is_canonical g.(entries) v ->
  Level.eq u v \/ clos_trans _ (ueq_step g.(entries)) u v.
Proof.
intros g u v Hr Hv.
apply eq_alt_iff in Hr; destruct Hr as [Hr|Hr]; [intuition|].
apply clos_rst_rst1n_iff in Hr; induction Hr as [u|u v w [H|H] _ IH].
+ left; reflexivity.
+ specialize (IH Hv).
  destruct IH as [IH|IH].
  - rewrite IH in H; right; apply t_step; assumption.
  - right; eapply t_trans; [eapply t_step|]; eassumption.
+ specialize (IH Hv); destruct IH as [IH|IH].
  - rewrite IH in H; elim is_canonical_minimal with g.(entries) w u; assumption.
  - apply clos_trans_t1n_iff in IH; destruct IH as [w Hw|w z Hw IH].
    { left; destruct H as [? Hrw1 H], Hw as [? Hrw2 Hw].
      apply UMap.find_1 in H; apply UMap.find_1 in Hw.
      replace w0 with w1 in * by congruence.
      rewrite Hrw1, Hrw2; reflexivity. }
    { right; destruct H as [? Hrw1 H], Hw as [? Hrw2 Hw].
      apply UMap.find_1 in H; apply UMap.find_1 in Hw.
      replace w0 with w1 in * by congruence.
      rewrite Hrw1, <- Hrw2; apply clos_trans_t1n_iff; assumption. }
Qed.

Print Transparent Dependencies is_canonical_rt.

Definition tip g u :=
  {| univ := u;
    ltle := UMap.empty bool;
    gtge := USet.empty;
    rank := 0;
    klvl := 0;
    ilvl := g.(index)
  |}.

Definition repr (g : Universes) (u : Level.t) : canonical_node.
Proof.
refine (
  Fix g.(ult_trans_wf) (fun u => _)
  (fun u repr =>
    let ans := UMap.find u g.(entries) in
    match ans as elt return
      match elt with
      | None => True
      | Some n => UMap.MapsTo u n g.(entries)
      end -> _
    with
    | None => fun _ => tip g u
    | Some (Canonical c) => fun _ => c
    | Some (Equiv v) => fun rw => repr v _
    end _
  )
  u
).
+ eapply ult_step_eq, rw; reflexivity.
+ remember ans as elt; destruct elt as [v|].
  - apply UMap.find_2; symmetry; assumption.
  - trivial.
Defined.

Lemma Fix_spec : forall A (R : relation A) (p : well_founded R) (P : A -> Type)
  (F : (forall x : A, (forall y : A, R y x -> P y) -> P x)) (Q : forall x, P x -> Type),
  (forall (x : A) a, (forall y r, Q y (Fix_F P F (a y r))) -> Q x (F x (fun y r => @Fix_F _ _ P F y (a y r)))) ->
  forall x, Q x (Fix p P F x).
Proof.
intros A R p P F Q HF x; unfold Fix.
set (a := p x); clearbody a.
revert x a.
refine (fix spec x a {struct a} := _).
destruct a; cbn; apply HF.
intros y r; apply spec.
Qed.

Lemma repr_spec : forall (g : Universes) u,
  UMap.In u g.(entries) -> Repr g.(entries) u (repr g u).
Proof.
intros g u Hu.
unfold repr; revert Hu.
match goal with [ |- context [Fix _ _ ?F] ] => set (f := F) in * end.
apply Fix_spec; clear u; intros u a IH Hu.
unfold f at 1; clearbody f.
set (p := (match
           UMap.find u (entries g) as o
           return
             (o = UMap.find u (entries g) ->
              match o with
              | Some n => UMap.MapsTo u n (entries g)
              | None => True
              end)
         with
         | Some v =>
             fun Heqelt : Some v = UMap.find u (entries g) =>
             UMap.find_2 (eq_sym Heqelt)
         | None => fun _ : None = UMap.find u (entries g) => I
         end eq_refl)); clearbody p.
revert p.
remember (UMap.find u (entries g)) as elt.
destruct elt as [[n|v]|]; intros p.
+ exists u; [|assumption].
  reflexivity.
+ refine (let IH := IH v _ _ in _); [| |clearbody IH].
  { eapply ult_step_eq; intuition eauto. }
  { eapply ult_complete, ult_step_eq; intuition eauto. }
  destruct IH as [w HR Hw].
  exists w; [|assumption].
  transitivity v; [|assumption].
  apply rst_step; left; econstructor; intuition.
+ apply F.in_find_iff in Hu; intuition.
Qed.

(* Lemma Repr_fun : forall (g : Universes) u n1 n2,
  Repr g.(entries) u n1 -> Repr g.(entries) u n2 -> n1 = n2.
Proof.
 *)

Lemma repr_is_canonical : forall (g : Universes) u,
  UMap.In u g.(entries) -> is_canonical g.(entries) (repr g u).(univ).
Proof.
intros g u Hu.
apply repr_spec in Hu; destruct Hu as [v Hu Hv].
exists (repr g u); [reflexivity|].
assert (Heq : Level.eq v (repr g u).(univ)).
{ apply g.(ueq_canonical) in Hv; assumption. }
rewrite <- Heq; assumption.
Qed.

Lemma repr_rel_eq : forall (g : Universes) u,
  UMap.In u g.(entries) -> Rel.eq g.(entries) u (repr g u).(univ).
Proof.
intros g u Hu.
apply repr_spec in Hu; destruct Hu as [v Hu Hv].
transitivity v; [assumption|].
apply rst_step; right; rewrite g.(ueq_canonical); [reflexivity|eassumption].
Qed.

Lemma repr_is_In : forall (g : Universes) u,
  UMap.In u g.(entries) -> UMap.In (repr g u).(univ) g.(entries).
Proof.
intros g u Hu.
assert (is_canonical g.(entries) (repr g u).(univ)) by apply repr_is_canonical, Hu.
destruct H as [n Hn H].
exists (Canonical n); assumption.
Qed.

(* Reindexes the given universe, using the next available index. *)
(* let use_index g u =
  let u = repr g u in
  let g = change_node g { u with ilvl = g.index } in
  assert (g.index > min_int);
  { g with index = g.index - 1 }
*)

(* [safe_repr] is like [repr] but if the graph doesn't contain the
   searched universe, we add it. *)
Program Definition safe_repr (g : Universes) (u : Level.t) :
  Universes * canonical_node :=
let ans := UMap.find u g.(entries) in
match ans as elt return
  match elt with
  | None => ~ UMap.In u g.(entries)
  | Some n => UMap.MapsTo u n g.(entries)
  end -> _
with
| None =>
  fun rw =>
  let can := tip g u in
  let g := {|
    index := N.pred g.(index);
    entries := UMap.add u (Canonical can) g.(entries);
    n_nodes := N.succ g.(n_nodes);
    n_edges := g.(n_edges)
  |} in
  let Hltu : forall v, ~ ult_step g.(entries) u v := _ in
  ({| ugraph := g |}, can)
| Some (Equiv v) => fun rw => (g, repr g v)
| Some (Canonical c) => fun _ => (g, c)
end _.

Next Obligation.
intros g u ? ? ? ? v Hv.
destruct Hv as [n Hu Hv|z Heq Hv].
+ apply UMapFacts.F.add_mapsto_iff in Hu; destruct Hu; [|now intuition].
  replace n with can in * by intuition congruence.
  apply -> UMapFacts.F.empty_in_iff in Hv; assumption.
+ apply UMapFacts.F.add_mapsto_iff in Hv; destruct Hv; intuition (eauto || congruence).
Qed.

Next Obligation.
intros g u ? ? ? g0 ?.
assert (Hwf := g.(ult_trans_wf)).
unfold g0 in *; cbn; clear g0; intros v.
specialize (Hwf v); induction Hwf as [v Hv IH]; constructor; intros w Hw.
destruct (Level.eq_dec u v) as [Hrw|Hd].
+ rewrite <- Hrw in Hw; eelim Hltu; eassumption.
+ apply IH; clear - Hw Hd.
  destruct Hw as [n Hv Hw|z Heq Hv].
  { apply UMap.add_3 in Hv; [|assumption].
    eapply ult_step_lt; eassumption.
  }
  { apply UMap.add_3 in Hv; [|assumption].
    eapply ult_step_eq; eassumption.
  }
Qed.

Next Obligation.
intros g u ? ? ? g0 ?.
intros v w Hlt.
destruct (Level.eq_dec u w) as [Hrw|Hd].
+ rewrite <- Hrw; eapply UMapFacts.F.add_in_iff; intuition.
+ apply F.add_neq_in_iff; [assumption|].
  assert (Hc : ~ Level.eq u v).
  { intros Hrw; eelim Hltu; rewrite Hrw; eassumption. }
  apply g.(ult_complete) with v.
  destruct Hlt.
  { eapply ult_step_lt; [|eassumption]; eapply UMap.add_3 in H; eassumption. }
  { eapply ult_step_eq; [eassumption|]; eapply UMap.add_3 in H0; eassumption. }
Qed.

Next Obligation.
intros g u ? ? ? g0 ?.
clear - g; intros v n Hv.
apply F.add_mapsto_iff in Hv; destruct Hv as [Hv|Hv].
+ replace n with can in * by intuition congruence.
  unfold can, tip; cbn; now intuition.
+ apply g.(ueq_canonical); now intuition.
Qed.

Next Obligation.
intros g u ? ? ? ? ? v w m n Hv Hw Hr; cbn in *.
destruct (Level.eq_dec u v) as [Hrw|Hd].
+ exfalso; rewrite <- Hrw in Hv; clear v Hrw.
  apply F.add_mapsto_iff in Hv; intuition.
  replace m with can in * by congruence; clear m.
  apply F.empty_in_iff in Hw; assumption.
+ assert (Hv' : UMap.MapsTo v (Canonical m) (entries g)); [|clear Hv].
  { eapply UMap.add_3 in Hv; eassumption. }
  assert (Hw' : ~ Level.eq u w).
  { intros Hrw; rewrite <- Hrw in *; clear w Hrw.
    elim rw; eapply g.(ult_complete), ult_step_lt; eauto. }
  apply (g.(unv_topo_rel) v w); try assumption.
  destruct Hr as [z Hz Hr]; apply eq_alt_iff in Hz.
  assert (Hc : ~ Level.eq u z).
  { intros Hrw; rewrite Hrw in rw.
    apply F.add_mapsto_iff in Hr; destruct Hr as [Hr|Hr]; [|now intuition].
    replace n with can in * by intuition congruence.
    destruct Hz as [Hz|Hz]; [rewrite <- Hrw in Hz; now intuition|].
    clear - Hz Hw' Hrw.
    apply clos_rst_rst1n_iff in Hz; induction Hz; [now intuition|].
    

  destruct Hz as [Hz|Hz].
Admitted.

Next Obligation.
intros g u ? ? ?.
remember ans as elt; destruct elt; [apply UMap.find_2; intuition|apply F.not_find_in_iff; intuition].
Qed.

Check safe_repr.

Definition clean_ltle (g : Universes) (ltle : UMap.t bool) : UMap.t bool * bool :=
let fold u strict accu :=
  let v := (repr g u).(univ) in
  (UMap.add v strict (fst accu), if Level.eq_dec u v then snd accu else true)
in
UMap.fold fold ltle (UMap.empty bool, false).

Record clean_ltle_Spec g (m1 m2 : UMap.t bool) (chg : bool) : Prop := {
  cltle_l : forall u, UMap.In u m1 -> exists v, UMap.In v m2 /\ Rel.eq g u v;
  cltle_r : forall u, UMap.In u m2 -> exists v, UMap.In v m1 /\ Rel.eq g u v;
  cltle_u : forall u v, UMap.In u m1 -> UMap.In v m2 -> Rel.eq g u v -> Level.eq u v;
  cltle_b : if chg then True else UMap.Equal m1 m2
}.

Lemma clean_ltle_spec : forall (g : Universes) ltle
  (m : forall u, UMap.In u ltle -> UMap.In u g.(entries)),
  let '(ans, chg) := clean_ltle g ltle in clean_ltle_Spec g.(entries) ltle ans chg.
Proof.
intros g ltle p.
unfold clean_ltle; apply fold_rec; cbn in *.
+ intros m Hm; split.
  - intros u [b Hu]; eelim Hm; eassumption.
  - intros u Hu; apply F.empty_in_iff in Hu; elim Hu.
  - intros u v Hu Hv H.
    apply F.empty_in_iff in Hv; elim Hv.
  - intros u; rewrite F.empty_o .
    apply F.not_find_in_iff.
    intros [? ?]; eelim Hm; eassumption.
+ intros u b [accu chg] m1 m2 Hu Hm1 Hm2 Hspec; cbn in *; split.
  - intros v Hv.
    apply F.find_in_iff in Hv.
    rewrite (Hm2 _) in Hv.
    apply F.find_mapsto_iff in Hv; apply F.add_mapsto_iff in Hv.
    destruct Hv as [Hv|Hv].
    { exists (univ (repr g u)); split.
      + apply F.add_mapsto_iff; left; intuition.
      + rewrite <- (proj1 Hv); apply repr_rel_eq; apply p; eexists; eassumption.
    }
    { eapply cltle_l in Hspec; [|now intuition eauto].
      destruct Hspec as [w Hw]; exists w.
      split; [|now intuition].
      apply F.add_mapsto_iff.
Admitted.


Lemma clean_ltle_identity : forall (g : Universes) ltle,
  let ans := clean_ltle g ltle in
  snd ans = false -> UMap.Equal (fst ans) ltle.
Proof.
intros g init (* m *) ans.
unfold clean_ltle in ans.
unfold ans; apply fold_rec; cbn in *; clear.
+ intros m Hm _ x; rewrite F.empty_o.
  symmetry; apply F.not_find_in_iff.
  intros [b Hb]; elim (Hm x b); assumption.
+ intros u b [m b'] m1 m2 Hm Hm1 Hm2 IH H.
  destruct F.eq_dec; cbn in *.
  - specialize (IH H); subst.
    rewrite IH, <- e; symmetry; exact Hm2.
  - discriminate.
Qed.

(* Lemma findA_inA : forall A B eqb l v,
  @SetoidList.findA A B eqb l = Some v.
 *)
(*
Lemma clean_ltle_equiv : forall (g : Universes) ltle
  (m : forall u, UMap.In u ltle -> UMap.In u g.(entries)),
  let ans := clean_ltle g ltle m in
  SetoidList.equivlistA (RelationPairs.RelProd (Rel.eq g) eq) (UMap.elements ltle) (UMap.elements (fst ans)).
Proof.
intros g init m ans.
unfold clean_ltle in ans.
unfold ans; apply fold_rec; cbn [fst snd] in *; clear.
+ intros m Hm [accu b]; cbn in *.
  rewrite elements_empty.
  apply elements_Empty in Hm; rewrite Hm; intuition.
+ intros u b [m b'] m1 m2 Hm Hm1 Hm2 IH [v b0]; cbn [fst snd] in *.
  destruct (Level.eq_dec u v) as [Hrw|Hd].
  - split; intro HIn.
    { apply SetoidList.InA_eqA with (u, b); try typeclasses eauto.
      + split; unfold RelationPairs.RelCompFun; cbn.


  do 2 rewrite <- F.elements_mapsto_iff.
  specialize (IH (v, b0)).
  do 2 rewrite <- F.elements_mapsto_iff in IH.
  do 2 rewrite F.find_mapsto_iff; rewrite Hm2.
  rewrite
Qed.
*)

Definition clean_gtge (g : Universes) (gtge : USet.t) : USet.t * bool.
Proof.
refine (
  let fold u accu :=
    let v := (repr g u).(univ) in
    match Level.eq_dec u v with
    | left _ => accu
    | right _ => (USet.add v (USet.remove u (fst accu)), true)
    end
  in
  USet.fold fold gtge (gtge, false)
).
Defined.

Program Definition get_ltle (g : Universes) (n : canonical_node)
  (m : forall u, UMap.In u n.(ltle) -> UMap.In u g.(entries)) :
  UMap.t bool * canonical_node * Universes :=
let '(ans, chg) := clean_ltle g n.(ltle) m in
if chg then
  let sz := N.of_nat (UMap.cardinal n.(Univ.ltle)) in
  let sz2 := N.of_nat (UMap.cardinal ans) in
  let n := {|
    univ := n.(univ);
    Univ.ltle := ans;
    gtge := n.(gtge);
    rank := n.(rank);
    klvl := n.(klvl);
    ilvl := n.(ilvl)
  |} in
  let g := {|
    entries := UMap.add n.(univ) (Canonical n) g.(entries);
    index := g.(index);
    n_nodes := g.(n_nodes);
    n_edges := (g.(n_edges) + sz2) - sz
  |} in
  (ans, n, {| ugraph := g |})
else (n.(Univ.ltle), n, g).
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Check get_ltle.

Program Definition get_gtge (g : Universes) (n : canonical_node)
  (m : forall u, USet.In u n.(gtge) -> UMap.In u g.(entries)) :
  USet.t * canonical_node * Universes :=
let '(ans, chg) := clean_gtge g n.(gtge) in
if chg then
  let n := {|
    univ := n.(univ);
    Univ.gtge := ans;
    ltle := n.(ltle);
    rank := n.(rank);
    klvl := n.(klvl);
    ilvl := n.(ilvl)
  |} in
  let g := {|
    entries := UMap.add n.(univ) (Canonical n) g.(entries);
    index := g.(index);
    n_nodes := g.(n_nodes);
    n_edges := g.(n_edges)
  |} in
  (ans, n, {| ugraph := g |})
else (n.(gtge), n, g)
.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Check get_gtge.

Set Implicit Arguments.

Record btT (count : N) := {
  btT_traversed : list Level.t;
  btT_seen : USet.t;
  btT_count : N;
  btT_countlt : N.lt btT_count count;
  btT_univ : Universes
}.

Unset Implicit Arguments.

Program Definition btT_pred {c} (r : btT (N.succ c)) (p : c <> 0%N) : btT c :=
{|
  btT_traversed := r.(btT_traversed);
  btT_seen := r.(btT_seen);
  btT_count := N.pred c;
  btT_countlt := _;
  btT_univ := r.(btT_univ)
|}.
Next Obligation.
intros c r p.
eapply N.lt_pred_l; congruence.
Qed.

Program Definition btT_cast {c1 c2} (r : btT c1) (p : N.lt c1 c2) : btT c2 :=
{|
  btT_traversed := r.(btT_traversed);
  btT_seen := r.(btT_seen);
  btT_count := r.(btT_count);
  btT_countlt := _;
  btT_univ := r.(btT_univ)
|}.
Next Obligation.
intros c1 c2 r p.
eapply N.lt_trans; try eapply btT_countlt; eassumption.
Qed.

Program Definition btT_push {c} (r : btT c) (u : Level.t) : btT c :=
{|
  btT_traversed := cons u r.(btT_traversed);
  btT_seen := r.(btT_seen);
  btT_count := r.(btT_count);
  btT_countlt := r.(btT_countlt);
  btT_univ := r.(btT_univ)
|}.

Program Definition btT_reset {c1 c2} (r : btT c1) : btT (N.succ c2) :=
{|
  btT_traversed := r.(btT_traversed);
  btT_seen := r.(btT_seen);
  btT_count := c2;
  btT_countlt := _;
  btT_univ := r.(btT_univ)
|}.
Next Obligation.
intros; apply N.lt_succ_diag_r.
Qed.

Notation "t >>= u" := (match t return _ with inl x => u x | inr y => inr y end) (at level 45, u at level 200, right associativity).

Definition backward_traverse (g : Universes)
  (count : N) (u : Level.t) (m : UMap.In u g.(entries)) :
  btT count + Universes.
Proof.
refine (
Fix N.lt_wf_0 (fun count => btT (N.succ count) -> _ -> _ -> btT count + Universes)
  (fun count traverse r u m =>
  let g := r.(btT_univ) in
  match count as c return count = c -> _ with
  | N0 => fun _ => inr g
  | _ =>
    fun pf =>
    let n := repr g u in
    if USet.mem n.(univ) r.(btT_seen) then inl (btT_pred r _)
    else
      let seen' := USet.add n.(univ) r.(btT_seen) in
      let cleaned := get_gtge g n _ in
      let fold v (accu : btT count + Universes) : btT count + Universes :=
        accu >>= fun r =>
        traverse r.(btT_count) r.(btT_countlt) (btT_reset r) v m >>= fun r =>
        inl (btT_cast r _)
      in
      let r := @Build_btT _ r.(btT_traversed) seen' (N.pred count) _ (snd cleaned) in
      USet.fold fold (fst (fst cleaned)) (inl r) >>= fun r =>
      inl (btT_push r u)
  end eq_refl) count
    {| btT_count := count; btT_univ := g; btT_traversed := nil; btT_seen := USet.empty |} u m
).
+ congruence.
+ intros v Hv.
  admit.
+ apply btT_countlt.
+ apply N.lt_pred_l; congruence.
+ apply N.lt_succ_diag_r.
Qed.

Definition forward_traverse (g : Universes) (lvl : N) (n : canonical_node) (u : Level.t) : (list Level.t * Universes).
Proof.
refine (
Fix g.(ult_trans_wf) (fun u => _ )
  (fun u traverse n traversed =>
    let m := repr g u in
    match (m.(klvl) ?= lvl)%N with
    | Lt =>
      let gtge := if Level.eq_dec n.(univ) m.(univ) then USet.empty else USet.singleton n.(univ) in
      let '(ltle, m, g) := get_ltle g m _ in
      _
    | Eq =>
      if Level.eq_dec n.(univ) m.(univ) then (traversed, g)
      else _
    | Gt => (traversed, g)
    end
  )
  u n nil
).
+ admit.
admit.

let rec forward_traverse f_traversed g v_klvl x y =
  let y = repr g y in
  if y.klvl < v_klvl then begin
    let y = { y with klvl = v_klvl;
                      gtge = if x == y then LSet.empty
                            else LSet.singleton x.univ }
    in
    let g = change_node g y in
    let ltle, y, g = get_ltle g y in
    let f_traversed, g =
      LMap.fold (fun z _ (f_traversed, g) ->
        forward_traverse f_traversed g v_klvl y z)
      ltle (f_traversed, g)
    in
    y.univ::f_traversed, g
    end else if y.klvl = v_klvl && x != y then
      let g = change_node g
        { y with gtge = LSet.add x.univ y.gtge } in
      f_traversed, g
    else f_traversed, g

End Univ.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extraction Univ.

End Univ.

Extraction Univ.

(* Checks most of the invariants of the graph. For debugging purposes. *)
let check_universes_invariants g =
  let n_edges = ref 0 in
  let n_nodes = ref 0 in
  LMap.iter (fun l u ->
    match u with
    | Canonical u ->
      LMap.iter (fun v strict ->
          incr n_edges;
          let v = repr g v in
          assert (topo_compare u v = -1);
          if u.klvl = v.klvl then
            assert (LSet.mem u.univ v.gtge ||
                    LSet.exists (fun l -> u == repr g l) v.gtge))
        u.ltle;
      LSet.iter (fun v ->
        let v = repr g v in
        assert (v.klvl = u.klvl &&
            (LMap.mem u.univ v.ltle ||
             LMap.exists (fun l _ -> u == repr g l) v.ltle))
      ) u.gtge;
      assert (u.status = NoMark);
      assert (Level.equal l u.univ);
      assert (u.ilvl > g.index);
      assert (not (LMap.mem u.univ u.ltle));
      incr n_nodes
    | Equiv _ -> assert (not (Level.is_small l)))
    g.entries;
  assert (!n_edges = g.n_edges);
  assert (!n_nodes = g.n_nodes)

exception AbortBackward of universes
exception CycleDetected

(* Implementation of the algorithm described in § 5.1 of the following paper:

   Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
   new approach to incremental cycle detection and related
   problems. arXiv preprint arXiv:1112.0784. *)

(* [delta] is the timeout for backward search. It might be
    usefull to tune a multiplicative constant. *)
let get_delta g =
  int_of_float
    (min (float_of_int g.n_edges ** 0.5)
        (float_of_int g.n_nodes ** (2./.3.)))

let rec backward_traverse to_revert b_traversed count g x =
  let x = repr g x in
  let count = count - 1 in
  if count < 0 then begin
    revert_graph to_revert g;
    raise (AbortBackward g)
  end;
  if x.status = NoMark then begin
    x.status <- Visited;
    let to_revert = x.univ::to_revert in
    let gtge, x, g = get_gtge g x in
    let to_revert, b_traversed, count, g =
      LSet.fold (fun y (to_revert, b_traversed, count, g) ->
        backward_traverse to_revert b_traversed count g y)
        gtge (to_revert, b_traversed, count, g)
    in
    to_revert, x.univ::b_traversed, count, g
  end
  else to_revert, b_traversed, count, g

let rec forward_traverse f_traversed g v_klvl x y =
  let y = repr g y in
  if y.klvl < v_klvl then begin
    let y = { y with klvl = v_klvl;
                      gtge = if x == y then LSet.empty
                            else LSet.singleton x.univ }
    in
    let g = change_node g y in
    let ltle, y, g = get_ltle g y in
    let f_traversed, g =
      LMap.fold (fun z _ (f_traversed, g) ->
        forward_traverse f_traversed g v_klvl y z)
      ltle (f_traversed, g)
    in
    y.univ::f_traversed, g
    end else if y.klvl = v_klvl && x != y then
      let g = change_node g
        { y with gtge = LSet.add x.univ y.gtge } in
      f_traversed, g
    else f_traversed, g

let rec find_to_merge to_revert g x v =
  let x = repr g x in
  match x.status with
  | Visited -> false, to_revert   | ToMerge -> true, to_revert
  | NoMark ->
    let to_revert = x::to_revert in
    if Level.equal x.univ v then
      begin x.status <- ToMerge; true, to_revert end
    else
      begin
        let merge, to_revert = LSet.fold
          (fun y (merge, to_revert) ->
            let merge', to_revert = find_to_merge to_revert g y v in
            merge' || merge, to_revert) x.gtge (false, to_revert)
        in
        x.status <- if merge then ToMerge else Visited;
        merge, to_revert
      end
  | _ -> assert false

let get_new_edges g to_merge =
  (* Computing edge sets. *)
  let to_merge_lvl =
    List.fold_left (fun acc u -> LMap.add u.univ u acc)
      LMap.empty to_merge
  in
  let ltle =
    LMap.fold (fun _ n acc ->
      LMap.merge (fun _ strict1 strict2 ->
        match strict1, strict2 with
        | Some true, _ | _, Some true -> Some true
        | _, _ -> Some false)
        acc n.ltle)
      to_merge_lvl LMap.empty
  in
  let ltle, _ = clean_ltle g ltle in
  let ltle =
    LMap.merge (fun _ a strict ->
      match a, strict with
      | Some _, Some true ->
        (* There is a lt edge inside the new component. This is a
            "bad cycle". *)
        raise CycleDetected
      | Some _, Some false -> None
      | _, _ -> strict
    ) to_merge_lvl ltle
  in
  let gtge =
    LMap.fold (fun _ n acc -> LSet.union acc n.gtge)
      to_merge_lvl LSet.empty
  in
  let gtge, _ = clean_gtge g gtge in
  let gtge = LSet.diff gtge (LMap.domain to_merge_lvl) in
  (ltle, gtge)


let reorder g u v =
  (* STEP 1: backward search in the k-level of u. *)
  let delta = get_delta g in

  (* [v_klvl] is the chosen future level for u, v and all
      traversed nodes. *)
  let b_traversed, v_klvl, g =
    try
      let to_revert, b_traversed, _, g = backward_traverse [] [] delta g u in
      revert_graph to_revert g;
      let v_klvl = (repr g u).klvl in
      b_traversed, v_klvl, g
    with AbortBackward g ->
      (* Backward search was too long, use the next k-level. *)
      let v_klvl = (repr g u).klvl + 1 in
      [], v_klvl, g
  in
  let f_traversed, g =
    (* STEP 2: forward search. Contrary to what is described in
        the paper, we do not test whether v_klvl = u.klvl nor we assign
        v_klvl to v.klvl. Indeed, the first call to forward_traverse
        will do all that. *)
    forward_traverse [] g v_klvl (repr g v) v
  in

  (* STEP 3: merge nodes if needed. *)
  let to_merge, b_reindex, f_reindex =
    if (repr g u).klvl = v_klvl then
      begin
        let merge, to_revert = find_to_merge [] g u v in
        let r =
          if merge then
            List.filter (fun u -> u.status = ToMerge) to_revert,
            List.filter (fun u -> (repr g u).status <> ToMerge) b_traversed,
            List.filter (fun u -> (repr g u).status <> ToMerge) f_traversed
          else [], b_traversed, f_traversed
        in
        List.iter (fun u -> u.status <- NoMark) to_revert;
        r
      end
    else [], b_traversed, f_traversed
  in
  let to_reindex, g =
    match to_merge with
    | [] -> List.rev_append f_reindex b_reindex, g
    | n0::q0 ->
      (* Computing new root. *)
      let root, rank_rest =
        List.fold_left (fun ((best, rank_rest) as acc) n ->
          if n.rank >= best.rank then n, best.rank else acc)
          (n0, min_int) q0
      in
      let ltle, gtge = get_new_edges g to_merge in
      (* Inserting the new root. *)
      let g = change_node g
        { root with ltle; gtge;
          rank = max root.rank (rank_rest + 1);
          predicative = List.exists (fun n -> n.predicative) to_merge }
      in

      (* Inserting shortcuts for old nodes. *)
      let g = List.fold_left (fun g n ->
        if Level.equal n.univ root.univ then g else enter_equiv g n.univ root.univ)
        g to_merge
      in

      (* Updating g.n_edges *)
      let oldsz =
        List.fold_left (fun sz u -> sz+LMap.cardinal u.ltle)
          0 to_merge
      in
      let sz = LMap.cardinal ltle in
      let g = { g with n_edges = g.n_edges + sz - oldsz } in

      (* Not clear in the paper: we have to put the newly
          created component just between B and F. *)
      List.rev_append f_reindex (root.univ::b_reindex), g

  in

  (* STEP 4: reindex traversed nodes. *)
  List.fold_left use_index g to_reindex

(* Assumes [u] and [v] are already in the graph. *)
(* Does NOT assume that ucan != vcan. *)
let insert_edge strict ucan vcan g =
  try
    let u = ucan.univ and v = vcan.univ in
    (* do we need to reorder nodes ? *)
    let g = if topo_compare ucan vcan <= 0 then g else reorder g u v in

    (* insert the new edge in the graph. *)
    let u = repr g u in
    let v = repr g v in
    if u == v then
      if strict then raise CycleDetected else g
    else
      let g =
        try let oldstrict = LMap.find v.univ u.ltle in
            if strict && not oldstrict then
              change_node g { u with ltle = LMap.add v.univ true u.ltle }
            else g
        with Not_found ->
          { (change_node g { u with ltle = LMap.add v.univ strict u.ltle })
            with n_edges = g.n_edges + 1 }
      in
      let v, g =
        if not u.predicative || v.predicative then v, g
        else
          let v = { v with predicative = true } in
          v, change_node g v
      in
      if u.klvl <> v.klvl || LSet.mem u.univ v.gtge then g
      else
        let v = { v with gtge = LSet.add u.univ v.gtge } in
        change_node g v
  with
  | CycleDetected as e -> raise e
  | e ->
    (** Unlikely event: fatal error or signal *)
    let () = cleanup_universes g in
    raise e
