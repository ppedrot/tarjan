Require FSets FMaps NArith Wellfounded.
Require Import Setoid Morphisms BinNat Relations.

Set Primitive Projections.

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


(* Instance Proper_ult_step *)

(*
let check_universes_invariants g =
  let n_edges = ref 0 in
  let n_nodes = ref 0 in
  UMap.iter (fun l u ->
    match u with
    | Canonical u ->
      let check_arc strict v =
        incr n_edges;
        let v = repr g v in
        assert (idx_of_can u < idx_of_can v);
        if u.klvl = v.klvl then
          assert (List.memq u.univ v.gtge ||
                  List.memq u (List.map (repr g) v.gtge))
      in
      List.iter (check_arc true) u.lt;
      List.iter (check_arc false) u.le;
      List.iter (fun v ->
        let v = repr g v in
        assert (v.klvl = u.klvl &&
            (List.memq u.univ v.le ||
             List.memq u.univ v.lt ||
             List.memq u (List.map (repr g) v.le) ||
             List.memq u (List.map (repr g) v.lt)))
      ) u.gtge;
      assert (u.status = NoMark);
      assert (Level.equal l u.univ);
      assert (u.ilvl > g.index);
      assert (CList.duplicates Level.equal (u.univ::u.lt@u.le) = []);
      incr n_nodes
    | Equiv _ -> assert (not (Level.is_small l)))
    g.entries;
  assert (!n_edges = g.n_edges);
  assert (!n_nodes = g.n_nodes)
*)

Record Universes := {
  ugraph :> universes;
  ult_trans_wf : well_founded (Basics.flip (ult_step ugraph.(entries)));
  ult_complete : forall u v, ult_step ugraph.(entries) u v -> UMap.In u ugraph.(entries) -> UMap.In v ugraph.(entries);
  ueq_canonical : forall u n, UMap.MapsTo u (Canonical n) ugraph.(entries) -> Level.eq u n.(univ)
}.

Module Rel.

Definition eq (g : Universes) (u v : Level.t) := clos_refl_sym_trans _ (ueq_step g.(entries)) u v.

End Rel.

(* Low-level function : makes u an alias for v.
   Does not removes edges from n_edges, but decrements n_nodes.
   u should be entered as canonical before.  *)
(*
let enter_equiv g u v =
  { entries =
      UMap.modify u (fun _ a ->
        match a with
        | Canonical n ->
          n.status <- NoMark;
          Equiv v
        | _ -> assert false) g.entries;
    index = g.index;
    n_nodes = g.n_nodes - 1;
    n_edges = g.n_edges }
*)

(* Low-level function : changes data associated with a canonical node.
   Resets the mutable fields in the old record, in order to avoid breaking
   invariants for other users of this record.
   n.univ should already been inserted as a canonical node. *)
(*
let change_node g n =
  { g with entries =
      UMap.modify n.univ
        (fun _ a ->
          match a with
          | Canonical n' ->
            n'.status <- NoMark;
            Canonical n
          | _ -> assert false)
        g.entries }
*)

Definition repr (g : Universes) (u : Level.t) (m : UMap.In u g.(entries)) : canonical_node.
Proof.
refine (
  Fix g.(ult_trans_wf) (fun u => UMap.In u g.(entries) -> _)
  (fun u repr m =>
    let ans := UMap.find u g.(entries) in
    match ans as elt return
      match elt with
      | None => ~ UMap.In u g.(entries)
      | Some n => UMap.MapsTo u n g.(entries)
      end -> _
    with
    | None => fun rw => False_rect _ (rw m)
    | Some (Canonical c) => fun _ => c
    | Some (Equiv v) => fun rw => repr v _ _
    end _
  )
  u m
).
+ eapply ult_step_eq, rw; reflexivity.
+ eapply g.(ult_complete); [|exists (Equiv v); eassumption].
  eapply ult_step_eq, rw; reflexivity.
+ remember ans as elt; destruct elt as [v|].
  - apply UMap.find_2; symmetry; assumption.
  - intros [v Hv]; apply UMap.find_1 in Hv; unfold ans in *; exfalso; congruence.
Defined.

(* Reindexes the given universe, using the next available index. *)
(* let use_index g u =
  let u = repr g u in
  let g = change_node g { u with ilvl = g.index } in
  assert (g.index > min_int);
  { g with index = g.index - 1 }
*)

Definition canonical g u :=
  {| univ := u;
    ltle := UMap.empty bool;
    gtge := USet.empty;
    rank := 0;
  (*         predicative = Level.is_set u; *)
    klvl := 0;
    ilvl := g.(index)
  |}.

(* [safe_repr] is like [repr] but if the graph doesn't contain the
   searched universe, we add it. *)
Definition safe_repr (g : Universes) (u : Level.t) :
  Universes * canonical_node.
Proof.
refine (
  let ans := UMap.find u g.(entries) in
  match ans as elt return
    match elt with
    | None => ~ UMap.In u g.(entries)
    | Some n => UMap.MapsTo u n g.(entries)
    end -> _
  with
  | None =>
    fun rw =>
    let can := canonical g u in
    let g := {|
      index := N.pred g.(index);
      entries := UMap.add u (Canonical can) g.(entries);
      n_nodes := N.succ g.(n_nodes);
      n_edges := g.(n_edges)
    |} in
    let Hltu : forall v, ~ ult_step g.(entries) u v := _ in
    ({| ugraph := g |}, can)
  | Some (Equiv v) => fun rw => (g, repr g v _)
  | Some (Canonical c) => fun _ => (g, c)
  end _
).
+ eapply g.(ult_complete); [|eexists; apply rw]; eapply ult_step_eq, rw; reflexivity.
+ intros v Hv.
  destruct Hv as [n Hu Hv|z Heq Hv].
  - apply UMapFacts.F.add_mapsto_iff in Hu; destruct Hu; [|now intuition].
    replace n with can in * by intuition congruence.
    apply -> UMapFacts.F.empty_in_iff in Hv; assumption.
  - apply UMapFacts.F.add_mapsto_iff in Hv; destruct Hv; intuition (eauto || congruence).
+ assert (Hwf := g0.(ult_trans_wf)).
  unfold g in *; cbn; clear g; intros v.
  specialize (Hwf v); induction Hwf as [v Hv IH]; constructor; intros w Hw.
  destruct (Level.eq_dec u v) as [Hrw|Hd].
  - rewrite <- Hrw in Hw; eelim Hltu; eassumption.
  - apply IH; clear - Hw Hd.
    destruct Hw as [n Hv Hw|z Heq Hv].
    { apply UMap.add_3 in Hv; [|assumption].
      eapply ult_step_lt; eassumption.
    }
    { apply UMap.add_3 in Hv; [|assumption].
      eapply ult_step_eq; eassumption.
    }
+ intros v w Hlt Hi.
  destruct (Level.eq_dec u w) as [Hrw|Hd].
  - rewrite <- Hrw; eapply UMapFacts.F.add_in_iff; intuition.
  - apply F.add_neq_in_iff; [assumption|].
    assert (Hc : ~ Level.eq u v).
    { intros Hrw; eelim Hltu; rewrite Hrw; eassumption. }
    apply g0.(ult_complete) with v; [|eapply F.add_neq_in_iff; eassumption].
    destruct Hlt.
    { eapply ult_step_lt; [|eassumption]; eapply UMap.add_3 in H; eassumption. }
    { eapply ult_step_eq; [eassumption|]; eapply UMap.add_3 in H0; eassumption. }
+ clear - g0; intros v n Hv.
  apply F.add_mapsto_iff in Hv; destruct Hv as [Hv|Hv].
  - replace n with can in * by intuition congruence.
    unfold can, canonical; cbn; now intuition.
  - apply g0.(ueq_canonical); now intuition.
+ remember ans as elt; destruct elt; [apply UMap.find_2; intuition|apply F.not_find_in_iff; intuition].
Defined.

Definition order u v :=
match (u.(klvl) ?= v.(klvl))%N with
| Lt => Lt
| Gt => Gt
| Eq => (u.(ilvl) ?= v.(ilvl))%N
end.

Definition elements_dep {A} (m : UMap.t A) : list {p : UMap.key * A | match p with (k, x) => UMap.MapsTo k x m end}.
Proof.
pose (l := UMap.elements m).
assert (Hin := @UMap.elements_2 _ m).
fold l in Hin.
clearbody l; revert Hin; induction l as [|x l IHl]; intros Hin.
+ exact nil.
+ refine (cons (exist _ x _) (IHl _)).
  - clear - Hin; destruct x; apply Hin; constructor; reflexivity.
  - clear - Hin; intros y l' Hy; apply Hin.
    apply SetoidList.InA_cons_tl, Hy.
Defined.

(** Inefficient, but UMap does not feature the right interface *)
Definition map_fold_strong {A B} (m : UMap.t A)
  (f : forall (k : UMap.key) (x : A), UMap.MapsTo k x m -> B -> B)
  (i : B) : B :=
    List.fold_right (fun p accu => match p with exist _ (x, k) p => f x k p accu end) i (elements_dep m).

Definition set_fold_strong {A} (m : USet.t)
  (f : forall (k : USet.elt), USet.In k m -> A -> A)
  (i : A) : A.
Proof.
refine (
  USet.fold (fun k accu =>
    let ans := USet.mem k m in
    match ans as elt return ans = elt -> A with
    | false => fun _ => accu
    | true => fun H => f k (USet.mem_2 H) accu
    end eq_refl) m i
).
Defined.

Definition clean_ltle (g : Universes) (ltle : UMap.t bool)
  (m : forall u, UMap.In u ltle -> UMap.In u g.(entries)) : UMap.t bool * bool.
Proof.
refine (
  let fold u strict p accu :=
    let v := (repr g u _).(univ) in
    match Level.compare u v with
    | OrderedType.EQ _ => accu
    | OrderedType.LT _ | OrderedType.GT _ =>
      let accu := UMap.remove u (fst accu) in
      if andb (negb strict) (UMap.mem v accu) then (accu, true)
      else (UMap.add v strict accu, true)
    end
  in
  map_fold_strong ltle fold (ltle, false)
).
+ apply m; exists strict; assumption.
Defined.

Lemma clean_ltle_spec : forall g ltle m,
  let ans := clean_ltle g ltle m in
  (forall u, UMap.In u (fst ans) -> is_canonical g.(entries) u)
(*   /\ (SetoidList.equivlistA (RelationPairs.RelProd (Rel.eq g) eq) (UMap.elements ltle) (UMap.elements (fst ans))) *)
.
Proof.
intros g us m ans.
unfold clean_ltle, map_fold_strong in ans.
let t := eval red in ans in match t with UMap.fold ?F _ _ => set (f := F) in * end.
pattern us in f.
let t := eval red in f in match t with pattern  end.
pattern ans.
apply fold_rec_nodep.


Qed.

Definition clean_gtge (g : Universes) (gtge : USet.t)
  (m : forall u, USet.In u gtge -> UMap.In u g.(entries)) : USet.t * bool.
Proof.
refine (
  let fold u strict accu :=
    let v := (repr g u _).(univ) in
    match Level.compare u v with
    | OrderedType.EQ _ => accu
    | _ => (USet.add v (USet.remove u (fst accu)), true)
    end
  in
  set_fold_strong gtge fold (gtge, false)
).
+ apply m; assumption.
Defined.

Definition get_ltle (g : Universes) (n : canonical_node)
  (m : forall u, UMap.In u n.(ltle) -> UMap.In u g.(entries)) :
  UMap.t bool * canonical_node * Universes.
Proof.
refine (
  let (ltle, chgt_ltle) := clean_ltle g n.(ltle) m in
  if chgt_ltle then
    let sz := N.of_nat (UMap.cardinal n.(Univ.ltle)) in
    let sz2 := N.of_nat (UMap.cardinal ltle) in
    let n := {|
      univ := n.(univ);
      Univ.ltle := ltle;
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
    (ltle, n, {| ugraph := g |})
  else (n.(Univ.ltle), n, g)
).
+ intros u.
  assert (Hwf := g0.(ult_trans_wf) u).
  induction Hwf as [u Hu IH].
  
Defined.

(* [get_ltle] and [get_gtge] return ltle and gtge arcs.
   Moreover, if one of these lists is dirty (e.g. points to a
   non-canonical node), these functions clean this node in the
   graph by removing some duplicate edges *)
let get_ltle g u =
  let ltle, chgt_ltle = clean_ltle g u.ltle in
  if not chgt_ltle then u.ltle, u, g
  else
    let sz = LMap.cardinal u.ltle in
    let sz2 = LMap.cardinal ltle in
    let u = { u with ltle } in
    let g = change_node g u in
    let g = { g with n_edges = g.n_edges + sz2 - sz } in
    u.ltle, u, g


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

let get_gtge g u =
  let gtge, chgt_gtge = clean_gtge g u.gtge in
  if not chgt_gtge then u.gtge, u, g
  else
    let u = { u with gtge } in
    let g = change_node g u in
    u.gtge, u, g

(* [revert_graph] rollbacks the changes made to mutable fields in
   nodes in the graph.
   [to_revert] contains the touched nodes. *)
let revert_graph to_revert g =
  List.iter (fun t ->
    match LMap.find t g.entries with
    | Equiv _ -> ()
    | Canonical t ->
      t.status <- NoMark) to_revert

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
