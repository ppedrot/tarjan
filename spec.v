Require FSets FMaps NArith Wellfounded.
Require Import Program Setoid Morphisms BinNat Relations.

Module Spec
  (Level : OrderedType.OrderedType)
  (UMap : FMapInterface.Sfun(Level))
  (USet : FSetInterface.Sfun(Level))
.

Module Import USetFacts := FSetFacts.WFacts_fun(Level)(USet).
Module Import UMapFacts := FMapFacts.WProperties_fun(Level)(UMap).

Record canonical_node :=
{ univ: Level.t;
  ltle: UMap.t bool;
  gtge: USet.t;
  rank : N;
  klvl: N;
  ilvl: N
}.

Definition order u v :=
match (u.(klvl) ?= v.(klvl))%N with
| Lt => Lt
| Gt => Gt
| Eq => (u.(ilvl) ?= v.(ilvl))%N
end.

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

Module Rel.

Definition compose {A} (R1 R2 : relation A) : relation A :=
  fun x y => exists z, R1 x y /\ R2 y z.

Definition eq g (u v : Level.t) :=
  clos_refl_sym_trans _ (relation_disjunction (ueq_step g) Level.eq) u v.

Definition le g (u v : Level.t) :=
  eq g u v \/ clos_trans _ (compose (compose (eq g) (ule_step g)) (eq g)) u v.

End Rel.

Record Repr g u n : Prop :=  {
  Repr_wit : Level.t;
  Repr_rel : Rel.eq g u Repr_wit;
  Repr_can : UMap.MapsTo Repr_wit (Canonical n) g
}.

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

End Spec.
