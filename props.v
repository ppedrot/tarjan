Require FSets FMaps NArith Wellfounded.
Require Import Program Setoid Morphisms BinNat Relations.
Require Tarjan.spec.

Module Props
  (Level : OrderedType.OrderedType)
  (UMap : FMapInterface.Sfun(Level))
  (USet : FSetInterface.Sfun(Level))
.

Module Import USetFacts := FSetFacts.WFacts_fun(Level)(USet).
Module Import UMapFacts := FMapFacts.WProperties_fun(Level)(UMap).
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
+ rewrite Hu, Hv in *; eapply ule_step_eq; eassumption.
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
+ rewrite <- Hx, <- Hy; assumption.
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

Instance PreOrder_le : forall g, PreOrder (Rel.le g).
Proof.
intros g; split.
+ intros u; left; reflexivity.
+ intros u v w Hl Hr; right.


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
