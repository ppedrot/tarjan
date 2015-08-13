Require FSets FMaps NArith Wellfounded.
Require Import BinNat Relations.

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

Inductive ueq_step g : Level.t -> Level.t -> Prop :=
| ueq_step_eq : forall u v,
  UMap.MapsTo u (Equiv v) g ->
  ueq_step g u v.

Inductive ule_step g : Level.t -> Level.t -> Prop :=
| ule_step_le : forall u v n,
  UMap.MapsTo u (Canonical n) g ->
  UMap.MapsTo v false n.(ltle) ->
  ule_step g u v
| ule_step_eq : forall u v,
  UMap.MapsTo u (Equiv v) g ->
  ule_step g u v.

Inductive ult_step g : Level.t -> Level.t -> Prop :=
| ult_step_lt : forall u v n,
  UMap.MapsTo u (Canonical n) g ->
  UMap.In v n.(ltle) ->
  ult_step g u v
| ult_step_eq : forall u v,
  UMap.MapsTo u (Equiv v) g ->
  ult_step g u v.

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
  ult_trans_wf : well_founded (fun u v => clos_trans _ (ult_step ugraph.(entries)) v u);
  ult_complete : forall u v, ult_step ugraph.(entries) u v -> UMap.In u ugraph.(entries) -> UMap.In v ugraph.(entries)
}.

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
+ apply t_step, ult_step_eq, rw.
+ eapply g.(ult_complete); [|exists (Equiv v); eassumption].
  eapply ult_step_eq, rw.
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
    let can :=
      {| univ := u;
        ltle := UMap.empty bool;
        gtge := USet.empty;
        rank := 0;
(*         predicative = Level.is_set u; *)
        klvl := 0;
        ilvl := g.(index)
      |}
    in
    let g := {|
      index := N.pred g.(index);
      entries := UMap.add u (Canonical can) g.(entries);
      n_nodes := N.succ g.(n_nodes);
      n_edges := g.(n_edges)
    |} in
    ({| ugraph := g |}, can)
  | Some (Equiv v) => fun rw => (g, repr g v _)
  | Some (Canonical c) => fun _ => (g, c)
  end _
).
+ eapply g.(ult_complete); [|eexists; apply rw]; eapply ult_step_eq, rw.
+ unfold g in *; cbn; clear g; intros v.
  destruct (Level.eq_dec u v).
  - constructor; intros w Hw; exfalso.
    apply clos_trans_tn1_iff in Hw; induction Hw; [|assumption].
    induction H.
    {
      apply UMapFacts.F.add_mapsto_iff in H; destruct H; [|intuition congruence].
      replace n with can in * by intuition congruence.
      apply -> UMapFacts.F.empty_in_iff in H0; assumption.
    }
    {
      apply UMapFacts.F.add_mapsto_iff in H; destruct H; intuition congruence.
    }
  - assert (Hwf := g0.(ult_trans_wf) v); unfold can; clear can.
    induction Hwf as [v Hv IH]; constructor; intros w Hw.
    assert (Hd : ~ Level.eq u w).
    { clear - Hw n; intros Hrw; induction Hw.
      + (* inversion H; subst.
        - *) admit.
      + destruct (Level.eq_dec u y); now intuition.

    apply IH.

Defined.

(*
let rec safe_repr g u =
  let rec safe_repr_rec entries u =
    match UMap.find u entries with
    | Equiv v -> safe_repr_rec entries v
    | Canonical arc -> arc
  in
  try g, safe_repr_rec g.entries u
  with Not_found ->
    let can =
      { univ = u;
        lt = []; le = []; gtge = [];
        rank = if Level.is_small u then big_rank else 0;
        predicative = Level.is_set u;
        klvl = 0; ilvl = 0;
        status = NoMark }
    in
    let g = { g with
      entries = UMap.add u (Canonical can) g.entries;
      n_nodes = g.n_nodes + 1 }
    in
    let g = use_index g u in
    g, repr g u
*)

(* [idx_of_can u] returns a pair of integers. Using lexicographical order
   over this pair for different nodes can be used to know the relative
   position of both nodes in the topological order. *)
let idx_of_can u = u.klvl, u.ilvl

(* [get_ltle] and [get_gtge] return ltle and gtge arcs.
   Moreover, if one of these lists is dirty (e.g. points to a
   non-canonical node), these functions clean this node in the
   graph by removing some duplicate edges *)
let get_ltle g u =
  let lt = CList.map (fun u -> (repr g u).univ) u.lt in
  let le = CList.map (fun u -> (repr g u).univ) u.le in
  if List.for_all2 (==) lt u.lt &&
     List.for_all2 (==) le u.le then
    u.lt, u.le, u, g
  else
    let lt = CList.sort_uniquize Level.compare lt in
    let le = CList.sort_uniquize Level.compare le in
    let le = CList.subtract_sorted Level.compare le lt in
    let sz = List.length u.lt + List.length u.le in
    let sz2 = List.length lt + List.length le in
    let u = { u with lt; le } in
    let g = change_node g u in
    let g = { g with n_edges = g.n_edges + sz2 - sz } in
    u.lt, u.le, u, g

let get_gtge g u =
  let gtge = CList.map (fun u -> (repr g u).univ) u.gtge in
  if List.for_all2 (==) gtge u.gtge then u.gtge, u, g
  else
    let gtge = CList.sort_uniquize Level.compare gtge in
    let u = { u with gtge } in
    let g = change_node g u in
    u.gtge, u, g

(* [revert_graph] rollbacks the changes made to mutable fields in
   nodes in the graph.
   [to_revert] contains the touched nodes. *)
let revert_graph to_revert g =
  List.iter (fun t ->
    match UMap.find t g.entries with
    | Equiv _ -> ()
    | Canonical t ->
      t.status <- NoMark) to_revert

exception AbortBackward of universes * int
exception CycleDetected

(* Implementation of the algorithm described in § 5.1 of the following paper:

   Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
   new approach to incremental cycle detection and related
   problems. arXiv preprint arXiv:1112.0784. *)
(* Assumes [u] and [v] are already in the graph. *)
let insert_edge strict ucan vcan g =
  try
    let u = ucan.univ and v = vcan.univ in
    let g =
      (* STEP 1: do we need to reorder nodes ? *)
      if idx_of_can ucan <= idx_of_can vcan then g
      else begin
        (* STEP 2: backward search in the k-level of u. *)
        (* [delta] is the timeout for backward search. It might be
           usefull to tune a multiplicative constant. *)
        let delta =
          int_of_float
            (min (float_of_int g.n_edges ** 0.5)
               (float_of_int g.n_nodes ** (2./.3.)))
        in
        let rec backward_traverse to_revert b_traversed count g x =
          let x = repr g x in
          let count = count + 1 in
          if count >= delta then begin
            (* Backward search is too long, abort it and use
               the next k-level. *)
            let v_klvl = (repr g u).klvl + 1 in
            revert_graph to_revert g;
            raise (AbortBackward (g, v_klvl))
          end;
          if x.status = NoMark then begin
            x.status <- Visited;
            let to_revert = x.univ::to_revert in
            let gtge, x, g = get_gtge g x in
            let to_revert, b_traversed, count, g =
              List.fold_left (fun (to_revert, b_traversed, count, g) y ->
                backward_traverse to_revert b_traversed count g y)
                (to_revert, b_traversed, count, g) gtge
            in
            to_revert, x.univ::b_traversed, count, g
          end
          else to_revert, b_traversed, count, g
        in
        (* [v_klvl] is the chosen future level for u, v and all
           traversed nodes. *)
        let b_traversed, v_klvl, g =
          try
            let to_revert, b_traversed, _, g = backward_traverse [] [] (-1) g u in
            revert_graph to_revert g;
            let v_klvl = (repr g u).klvl in
            b_traversed, v_klvl, g
          with AbortBackward (g, v_klvl) -> [], v_klvl, g
        in
        let f_traversed, g =
          (* STEP 3: forward search. Contrary to what is described in
             the paper, we do not test whether v_klvl = u.klvl nor we assign
             v_klvl to v.klvl. Indeed, the first call to forward_traverse
             will do all that. *)
          let rec forward_traverse f_traversed g x y =
            let y = repr g y in
            if y.klvl < v_klvl then begin
              let y = { y with gtge = if x == y then [] else [x.univ];
                               klvl = v_klvl }
              in
              let g = change_node g y in
              let lt, le, y, g = get_ltle g y in
              let f_traversed, g =
                List.fold_left
                  (fun (f_traversed, g) z -> forward_traverse f_traversed g y z)
                  (f_traversed, g) (lt@le)
              in
              y.univ::f_traversed, g
             end else if y.klvl = v_klvl && x != y then
               let g = change_node g { y with gtge = x.univ::y.gtge } in
               f_traversed, g
             else f_traversed, g
          in
          forward_traverse [] g (repr g v) v
        in

        (* STEP 4: merge nodes if needed. *)
        let rec find_to_merge to_revert x =
          let x = repr g x in
          match x.status with
          | Visited -> false, to_revert   | ToMerge -> true, to_revert
          | NoMark ->
            let to_revert = x::to_revert in
            if Level.equal x.univ v then
              begin x.status <- ToMerge; true, to_revert end
            else
              begin
                let merge, to_revert = List.fold_left
                  (fun (merge, to_revert) y ->
                    let merge', to_revert = find_to_merge to_revert y in
                    merge' || merge, to_revert) (false, to_revert) x.gtge
                in
                x.status <- if merge then ToMerge else Visited;
                merge, to_revert
              end
          | _ -> assert false
        in
        let to_merge, b_reindex, f_reindex =
          if (repr g u).klvl = v_klvl then
            begin
              let merge, to_revert = find_to_merge [] u in
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

            (* Computing edge sets. *)
            let to_merge_lvl =
              List.sort Level.compare (List.map (fun u -> u.univ) to_merge)
            in
            let merge_neigh f =
              CList.sort_uniquize Level.compare
                (List.map (fun u -> (repr g u).univ)
                   (CList.map_append f to_merge))
            in
            let lt = merge_neigh (fun n -> n.lt) in
            (* There is a lt edge inside the new component. This is a
               "bad cycle". *)
            if not (CList.disjoint_sorted Level.compare lt to_merge_lvl) then
              raise CycleDetected;
            let le = merge_neigh (fun n -> n.le) in
            let le = CList.subtract_sorted Level.compare le to_merge_lvl in
            let le = CList.subtract_sorted Level.compare le lt in
            let gtge = merge_neigh (fun n -> n.gtge) in
            let gtge = CList.subtract_sorted Level.compare gtge to_merge_lvl in

            (* Inserting the new root. *)
            let g = change_node g
              { root with lt; le; gtge;
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
              List.fold_left (fun sz u -> sz+List.length u.lt) 0 to_merge +
              List.fold_left (fun sz u -> sz+List.length u.le) 0 to_merge
            in
            let sz = List.length le + List.length lt in
            let g = { g with n_edges = g.n_edges + sz - oldsz } in

            (* Not clear in the paper: we have to put the newly
               created component just between B and F. *)
            List.rev_append f_reindex (root.univ::b_reindex), g
        in

        (* STEP 5: reindex traversed nodes. *)
        List.fold_left use_index g to_reindex
      end
    in

    (* STEP 6: insert the new edge in the graph. *)
    let u = repr g u in
    let v = repr g v in
    if u == v then
      if strict then raise CycleDetected else g
    else
      let g =
        match strict,
          CList.mem_f Level.equal v.univ u.lt,
          CList.mem_f Level.equal v.univ u.le with
        | _, true, _ | false, _, true -> g
        | true, false, true ->
          change_node g
            { u with lt = v.univ :: u.lt;
              le = CList.except Level.equal v.univ u.le }
        | _, false, false ->
          let u = if strict then { u with lt = v.univ :: u.lt }
                            else { u with le = v.univ :: u.le }
          in
          let g = change_node g u in
          { g with n_edges = g.n_edges + 1 }
      in
      let v, g =
        if not u.predicative || v.predicative then v, g
        else
          let v = { v with predicative = true } in
          v, change_node g v
      in
      if u.klvl <> v.klvl || CList.mem_f Level.equal u.univ v.gtge then g
      else
        let v = { v with gtge = u.univ :: v.gtge } in
        change_node g v
  with
  | CycleDetected as e -> raise e

type constraint_type = Lt | Le | Eq

type explanation = (constraint_type * universe) list

exception Found_explanation of explanation

let get_explanation strict u v g =
  let v = repr g v in
  let visited_strict = ref UMap.empty in
  let rec traverse strict u =
    if u == v then
      if strict then None else Some []
    else if idx_of_can u > idx_of_can v then None
    else
      let visited =
        try not (UMap.find u.univ !visited_strict) || strict
        with Not_found -> false
      in
      if visited then None
      else begin
        visited_strict := UMap.add u.univ strict !visited_strict;
        try
          let f typ u' =
            match traverse (strict && typ = Le) (repr g u') with
            | None -> ()
            | Some exp -> raise (Found_explanation ((typ, make u') :: exp))
          in
          List.iter (f Lt) u.lt;
          List.iter (f Le) u.le;
          None
        with Found_explanation exp -> Some exp
      end
  in
  let u = repr g u in
  if u == v then [(Eq, make v.univ)]
  else match traverse strict u with Some exp -> exp | None -> assert false

let get_explanation strict u v g =
  if !Flags.univ_print then Some (get_explanation strict u v g)
  else None

(* To compare two nodes, we simply do a forward search.
   We implement two improvements:
   - we ignore nodes that are higher than the destination;
   - we do a BFS rather than a DFS because we expect to have a short
       path (typically, the shortest path has length 1)
 *)
let search_path strict u v g =
  let rec loop to_revert todo next_todo =
    match todo, next_todo with
    | [], [] -> false, to_revert (* No path found *)
    | [], _ -> loop to_revert next_todo []
    | (u, strict)::todo, _ ->
      if u.status = Visited || (u.status = WeakVisited && strict)
      then loop to_revert todo next_todo
      else
        let to_revert = if u.status = NoMark then u::to_revert else to_revert in
        u.status <- if strict then WeakVisited else Visited;
        let rec aux strict next_todo l cont =
          match l with
          | [] -> cont next_todo
          | u::l ->
            let u = repr g u in
            if u == v && not strict then true, to_revert
            else if idx_of_can u >= idx_of_can v then aux strict next_todo l cont
            else aux strict ((u, strict)::next_todo) l cont
        in
        aux false next_todo u.lt (fun next_todo ->
        aux strict next_todo u.le (fun next_todo ->
        loop to_revert todo next_todo))
  in
  if u == v then not strict
  else
    try
      let res, to_revert = loop [] [u, strict] [] in
      List.iter (fun u -> u.status <- NoMark) to_revert;
      res
    with e ->
      (** Unlikely event: fatal error or signal *)
      let () = cleanup_universes g in
      raise e
