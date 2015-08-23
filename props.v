Require FSets FMaps NArith Wellfounded.
Require Import Program Setoid Morphisms BinNat Relations Omega.
Require Tarjan.spec.

Obligation Tactic := idtac.

Module Props
  (Level : OrderedType.OrderedType)
  (UMap : FMapInterface.Sfun(Level))
  (USet : FSetInterface.Sfun(Level))
.

Module Import USetFacts := FSetFacts.WFacts_fun(Level)(USet).
Module Import UMapFacts := FMapFacts.WProperties_fun(Level)(UMap).

Fixpoint for_all {A} (P : A -> Prop) (l : list A) : Prop :=
match l with
| nil => True
| cons x l => P x /\ for_all P l
end.

Program Definition map_fold_strong {elt A} (m : UMap.t elt)
  (f : forall (k : Level.t) (e : elt), UMap.MapsTo k e m -> A -> A) (accu : A) : A :=
(fix fold_strong l accu :=
match l return for_all (fun p => UMap.MapsTo (fst p) (snd p) m) l -> A with
| nil => fun _ => accu
| cons (k, e) l => fun p => fold_strong l (f k e (proj1 p) accu) (proj2 p)
end) (UMap.elements m) accu _.
Next Obligation.
intros elt A m _ _.
assert (H := @UMap.elements_2 _ m).
set (l := UMap.elements m) in *; clearbody l; induction l as [|[k e] l]; cbn.
+ trivial.
+ split.
  - apply H, SetoidList.InA_cons_hd; reflexivity.
  - apply IHl; clear - H; intros k' e' Hm.
    apply H, SetoidList.InA_cons_tl; assumption.
Qed.

Program Definition set_fold_strong {A} (m : USet.t)
  (f : forall (k : Level.t), USet.In k m -> A -> A) (accu : A) : A :=
(fix fold_strong l accu :=
match l return for_all (fun p => USet.In p m) l -> A with
| nil => fun _ => accu
| cons k l => fun p => fold_strong l (f k (proj1 p) accu) (proj2 p)
end) (USet.elements m) accu _.
Next Obligation.
intros A m _ _.
assert (H := @USet.elements_2 m).
set (l := USet.elements m) in *; clearbody l; induction l as [|k l]; cbn.
+ trivial.
+ split.
  - apply H, SetoidList.InA_cons_hd; reflexivity.
  - apply IHl; clear - H; intros k' Hm.
    apply H, SetoidList.InA_cons_tl; assumption.
Qed.

Module Export Spec := spec.Spec(Level)(UMap)(USet).

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
Qed.

Instance Proper_rel_step : forall g, Proper (Level.eq ==> Level.eq ==> iff) (rel_step g).
Proof.
intros g; eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros u1 u2 Hu v1 v2 Hv Hrw.
destruct Hrw.
+ rewrite Hu, Hv in *; eapply rel_step_lt; eassumption.
+ rewrite Hu, Hv in *; eapply rel_step_eq; eassumption.
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

Instance Proper_compose : forall A (R1 R2 : relation A) R,
  Equivalence R ->
  Proper (R ==> R ==> iff) R1 ->
  Proper (R ==> R ==> iff) R2 ->
  Proper (R ==> R ==> iff) (Rel.compose R1 R2).
Proof.
intros A R1 R2 R HR HR1 HR2.
eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros x1 x2 Hx y1 y2 Hy [z [H1 H2]].
exists z; split.
+ rewrite <- Hx; assumption.
+ rewrite <- Hy; assumption.
Qed.

Instance Equivalence_eq : forall g, Equivalence (Rel.eq g).
Proof.
intros g.
destruct (clos_rst_is_equiv _ (relation_disjunction (ueq_step g) Level.eq)); split.
+ apply equiv_refl.
+ apply equiv_sym.
+ apply equiv_trans.
Qed.

Instance subrelation_eq : forall g, subrelation Level.eq (Rel.eq g).
Proof.
intros g u v H; apply rst_step; right; assumption.
Qed.

Instance Proper_le : forall g, Proper (Rel.eq g ==> Rel.eq g ==> iff) (Rel.le g).
Proof.
intros g.
eapply proper_sym_impl_iff_2; [now eauto|now eauto|].
intros u1 u2 Hu v1 v2 Hv [H|H].
+ left; rewrite <- Hu, <- Hv; assumption.
+ right; apply clos_trans_t1n_iff in H; apply clos_trans_t1n_iff.
  revert u2 v2 Hu Hv; induction H as [u1 v1 H|u1 w1 v1 H _ IH]; intros u2 v2 Hu Hv.
  - left; destruct H as [w [[z [Hzl Hzr]] Hwr]].
    rewrite Hu in Hzl; clear u1 Hu.
    exists w; split; [|rewrite Hwr; assumption].
    exists z; split; [assumption|assumption].
  - eright; [|apply IH; [reflexivity|assumption]].
    destruct H as [w [[z [Hzl Hzr]] Hwr]].
    rewrite Hu in Hzl; clear u1 Hu.
    exists w; split; [|rewrite Hwr; reflexivity].
    exists z; split; [assumption|assumption].
Qed.

Instance PreOrder_le : forall g, PreOrder (Rel.le g).
Proof.
intros g; split.
+ intros u; left; reflexivity.
+ intros u v w [Hl|Hl] [Hr|Hr].
  - rewrite Hl, Hr; left; reflexivity.
  - rewrite Hl; right; assumption.
  - rewrite <- Hr; right; assumption.
  - right; eapply t_trans; eassumption.
Qed.

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

Lemma rel_step_dec : forall g u v, {rel_step g u v} + {~ rel_step g u v}.
Proof.
intros g u v.
remember (UMap.find u g) as elt; destruct elt as [[n|w]|].
+ remember (UMap.mem v n.(ltle)) as b; destruct b.
  - left; eapply rel_step_lt; [apply F.find_mapsto_iff; now eauto|].
    apply UMapFacts.F.mem_in_iff; congruence.
  - right; intros Hc.
    destruct Hc as [w H Hi|w Heq H]; apply F.find_mapsto_iff in H; [|congruence].
    apply UMapFacts.F.mem_in_iff in Hi; congruence.
+ destruct (Level.eq_dec v w).
  - left; eapply rel_step_eq; [eassumption|]; apply F.find_mapsto_iff; congruence.
  - right; intros Hc.
    destruct Hc as [z H|z Heq H]; apply F.find_mapsto_iff in H; [congruence|].
    replace z with w in * by congruence; now intuition.
+ right; intros Hc.
  destruct Hc as [w H|w Heq H]; apply F.find_mapsto_iff in H; congruence.
Qed.

Lemma exists_extract : forall elt (f : Level.t -> elt -> bool) m,
  Proper (Level.eq ==> eq ==> eq) f ->
  (exists p, UMap.MapsTo (fst p) (snd p) m /\ f (fst p) (snd p) = true) ->
  {p | match p with (k, e) => f k e = true /\ UMap.MapsTo k e m end}.
Proof.
intros elt f m Hf.
pattern m; apply map_induction; clear - Hf.
+ intros m Hm H; exfalso.
  destruct H as [[k e] [H _]].
  eelim Hm; eassumption.
+ intros m1 m2 IH k e Hk Ha HS.
  remember (f k e) as b; destruct b.
  - exists (k, e); split; [now intuition|].
    apply F.find_mapsto_iff; rewrite Ha.
    apply UMapFacts.F.add_eq_o; reflexivity.
  - destruct IH as [[k' e'] [Hb Hm1]].
    { destruct HS as [[k' e'] [Hm Heq]].
      exists (k', e'); split; [|assumption].
      assert (Hd : ~ Level.eq k k').
      { intros Hc; rewrite <- Hc in *.
        specialize (Ha k); rewrite UMapFacts.F.add_eq_o in Ha; [|reflexivity].
        cbn in *; apply UMap.find_1 in Hm; congruence.
      }
      eapply UMap.add_3; [eassumption|].
      rewrite F.add_neq_mapsto_iff; [|eassumption].
      erewrite F.find_mapsto_iff, <- F.add_neq_o, <- Ha; [|eassumption].
      rewrite <- F.find_mapsto_iff; assumption.
    }
    exists (k', e'); split; [assumption|].
    rewrite F.find_mapsto_iff, Ha, <- F.find_mapsto_iff.
    assert (Hd : ~ Level.eq k k').
    { intros Hc; rewrite <- Hc in *.
      elim Hk; eexists; eassumption. }
    rewrite F.add_neq_mapsto_iff; eassumption.
Unshelve.
assumption.
Qed.

Lemma is_rel_source : forall g u, {v | rel_step g v u} + {forall v, ~ rel_step g v u}.
Proof.
intros g u.
pose (b := UMapFacts.exists_ (fun v _ => if rel_step_dec g v u then true else false) g).
assert (Hf : Proper (Level.eq ==> eq ==> eq) (fun v (_ : univ_entry) => if rel_step_dec g v u then true else false)).
{
  clear; intros v1 v2 Hv b ? <-.
  destruct rel_step_dec as [Hl|Hl];
  destruct rel_step_dec as [Hr|Hr]; trivial; exfalso;
  rewrite <- Hv in Hr; contradiction.
}
remember b as ex; destruct ex; symmetry in Heqex.
+ apply exists_iff in Heqex; [|assumption].
  refine (let He := exists_extract _ _ _ _ Heqex in _); clearbody He; clear Heqex.
  destruct He as [[v ?] [Heq Hm]].
  destruct rel_step_dec; [|congruence].
  left; exists v; assumption.
+ right; intros v Hv.
  assert (b = true); [|congruence].
  unfold b; rewrite exists_iff; [|assumption].
  assert (He : exists e, UMap.MapsTo v e g); [destruct Hv; firstorder|].
  destruct He as [e He].
  exists (v, e); split; cbn; [assumption|].
  destruct rel_step_dec; congruence.
Qed.

Instance clos_trans_inclusion : forall A,
  Proper (inclusion _ ==> inclusion _) (clos_trans A).
Proof.
intros A R1 R2 HR x1 x2 Heq.
induction Heq; [apply t_step|eapply t_trans; eassumption].
apply HR; assumption.
Qed.

Program Definition decide_acc g u :
  (Acc (rel_step g) u) + {v | clos_trans _ (rel_step g) v v} :=

Fix (Wf_nat.lt_wf)
  (fun size => forall u seen,
    size = UMap.cardinal g - UMap.cardinal seen ->
    (forall u, UMap.MapsTo u true seen -> Acc (rel_step g) u) ->
    ((Acc (rel_step g) u) + {v | clos_trans _ (rel_step g) v v})
  )
  (fun n decide_acc u seen Hrw Hseen =>
    match UMap.find u seen with
    | None => _
    | Some _ => _
    end
  )
  (UMap.cardinal g) u (UMap.empty bool) _ _.
Next Obligation.
intros.
.

Lemma decide_wf : forall g, 

Lemma ill_founded_has_cycle : forall g,
  ~ well_founded (rel_step g) -> {u | clos_trans _ (rel_step g) u u}.
Proof.
intros g Hg.
pose (is_source := fun g u (_ : univ_entry) => if is_rel_source g u then true else false).
assert (Hf : forall g, Proper (Level.eq ==> eq ==> eq) (is_source g)).
{
  unfold is_source; clear; intros g u1 u2 Hu e ? <-.
  destruct is_rel_source as [Hl|Hl];
  destruct is_rel_source as [Hr|Hr]; trivial; exfalso.
  + destruct Hl as [v Hv]; elim (Hr v); rewrite <- Hu; assumption.
  + destruct Hr as [v Hv]; elim (Hl v); rewrite Hu; assumption.
}
remember (UMap.cardinal g) as size.
assert (Hwf := Wf_nat.lt_wf size).
revert g Hg Heqsize; induction Hwf as [size _ IH]; intros g Hg Heq; subst.
remember (partition (is_source g) g) as p; symmetry in Heqp.
destruct p as [g1 g2].
remember (UMap.is_empty g1) as b; symmetry in Heqb; destruct b.
+ assert (H : forall u v, UMap.In u g -> rel_step g v u -> False).
  admit.
  admit.
+ assert (Hlt : (UMap.cardinal g1) <> 0).
  { intros Heq; rewrite <- UMapFacts.cardinal_Empty in Heq.
    apply UMap.is_empty_1 in Heq; congruence. }
  assert (Hsize : UMap.cardinal g1 + UMap.cardinal g2 = UMap.cardinal g).
  { symmetry; apply Partition_cardinal; eapply partition_Partition; eauto. }
  assert (Hi : {u | clos_trans _ (rel_step g2) u u}).
  { apply (IH (UMap.cardinal g2)); [omega| |reflexivity].
    clear - Heqp Hg; intros Hc; elim Hg; clear Hg.
    admit. }
  destruct Hi as [u Hu]; exists u.
  eapply clos_trans_inclusion; [|eassumption].
  admit.
Qed.



(*
Lemma rel_step_dec_l : forall g u, {v | rel_step g u v} + {forall v, ~ rel_step g u v}.
Proof.
intros g u.
remember (UMap.find u g) as elt; destruct elt as [[n|w]|].
+ SearchAbout UMap.Empty "dec".

remember (UMap.mem v n.(ltle)) as b; destruct b.
  - left; eapply rel_step_lt; [apply F.find_mapsto_iff; now eauto|].
    apply UMapFacts.F.mem_in_iff; congruence.
  - right; intros Hc.
    destruct Hc as [w H Hi|w Heq H]; apply F.find_mapsto_iff in H; [|congruence].
    apply UMapFacts.F.mem_in_iff in Hi; congruence.
+ destruct (Level.eq_dec v w).
  - left; eapply rel_step_eq; [eassumption|]; apply F.find_mapsto_iff; congruence.
  - right; intros Hc.
    destruct Hc as [z H|z Heq H]; apply F.find_mapsto_iff in H; [congruence|].
    replace z with w in * by congruence; now intuition.
+ right; intros Hc.
  destruct Hc as [w H|w Heq H]; apply F.find_mapsto_iff in H; congruence.
Qed.
*)

(*
Lemma wf_rel_step : forall g,
  well_founded (Basics.flip (rel_step g)) -> well_founded (rel_step g).
Proof.
intros g Hr u; specialize (Hr u); revert u Hr.
*)

End Props.
