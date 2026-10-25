/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part31


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem idxOf_succ_of_pair_infix_nodup {alpha : Type*} [DecidableEq alpha]
    {x y : alpha} {l : List alpha} (hl : l.Nodup)
    (hxy : [x, y] <:+: l) :
    l.idxOf y = l.idxOf x + 1 := by
  rw [List.infix_iff_prefix_suffix] at hxy
  rcases hxy with ⟨t, hpre, hsuf⟩
  rw [List.prefix_iff_eq_append] at hpre
  rw [List.suffix_iff_eq_append] at hsuf
  let a := l.take (l.length - t.length)
  let b := t.drop 2
  have hl' : a ++ [x, y] ++ b = l := by
    calc
      a ++ [x, y] ++ b = a ++ ([x, y] ++ b) := by simp
      _ = a ++ t := by
        rw [show [x, y] ++ b = t by simpa [b] using hpre]
      _ = l := by simpa [a] using hsuf
  have hn := hl' ▸ hl
  rw [← hl']
  simp only [List.idxOf_append]
  rw [List.nodup_append] at hn
  rcases hn with ⟨hnaxy, _hnb, _hdisjb⟩
  rw [List.nodup_append] at hnaxy
  rcases hnaxy with ⟨_hna, hnxy, hdisj⟩
  have hxA : x ∉ a := by
    intro hx
    exact (hdisj x hx x (by simp)) rfl
  have hyA : y ∉ a := by
    intro hy
    exact (hdisj y hy y (by simp)) rfl
  have hxyne : x ≠ y := by
    simpa using (List.nodup_cons.mp hnxy).1
  simp [hxA, hyA, hxyne]
  omega


theorem isAlternating_path_edge_iff_odd {V : Type*}
    {G M : SimpleGraph V} {u v : V}
    (halt : G.IsAlternating M) (p : G.Walk u v) (hp : p.IsPath)
    (hfirst : ¬ M.Adj (p.getVert 0) (p.getVert 1)) :
    ∀ i, i < p.length ->
      (M.Adj (p.getVert i) (p.getVert (i + 1)) ↔ Odd i) := by
  intro i hi
  induction i with
  | zero =>
      constructor
      · intro h
        exact False.elim (hfirst (by simpa only [p.getVert_zero] using h))
      · intro h
        rcases h with ⟨k, hk⟩
        omega
  | succ i ih =>
      have hi0 : i < p.length := by omega
      have hi2 : i + 2 ≤ p.length := by omega
      have hprev := p.adj_getVert_succ hi0
      have hnext := p.adj_getVert_succ hi
      have hne : p.getVert i ≠ p.getVert (i + 2) := by
        intro h
        have := hp.getVert_injOn (show i ≤ p.length by omega) hi2 h
        omega
      have ha : M.Adj (p.getVert i) (p.getVert (i + 1)) ↔
          ¬ M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
        simpa only [M.adj_comm, Nat.succ_eq_add_one,
          Nat.add_assoc, Nat.reduceAdd] using
            halt hne hprev.symm hnext
      have hflip : M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) ↔
          ¬ M.Adj (p.getVert i) (p.getVert (i + 1)) := by
        tauto
      have ih' := ih hi0
      rw [hflip, ih', Nat.odd_add_one]


theorem fkIsingSquare_localMate_infix_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
    [(.dart (e, side) : FKIsingSquareMedialCarrier n),
        .dart (FKIsingMedialDart.localMate omega (e, side))] <:+:
        fkIsingSquareExplorationOrder n hn omega ∨
      [(.dart (FKIsingMedialDart.localMate omega (e, side)) :
          FKIsingSquareMedialCarrier n), .dart (e, side)] <:+:
        fkIsingSquareExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareLoopGraph n hn omega).Adj
      (.dart (e, side))
      (.dart (FKIsingMedialDart.localMate omega (e, side))) :=
    (fkIsingSquareLoopGraph_adj_dart_iff n hn omega
      (e, side) _).2 (Or.inl rfl)
  apply Walk.infix_support_iff_mem_edges.mpr
  apply fkIsingSquareExplorationPath_mem_edges_of_adj n hn omega h hadj


theorem fkIsingSquare_localMate_idxOf_adjacent
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
    (fkIsingSquareExplorationOrder n hn omega).idxOf
        (.dart (FKIsingMedialDart.localMate omega (e, side))) =
      (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (e, side)) + 1 ∨
    (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (e, side)) =
      (fkIsingSquareExplorationOrder n hn omega).idxOf
        (.dart (FKIsingMedialDart.localMate omega (e, side))) + 1 := by
  rcases fkIsingSquare_localMate_infix_explorationOrder
      n hn omega e side h with hforward | hbackward
  · exact Or.inl (idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareExplorationOrder_nodup n hn omega) hforward)
  · exact Or.inr (idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareExplorationOrder_nodup n hn omega) hbackward)


theorem fkIsingSquare_localMate_infix_of_counterclockwise
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (hccw : (fkIsingSquareSideCorner side).2 = .counterclockwise)
    (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
    [(.dart (e, side) : FKIsingSquareMedialCarrier n),
        .dart (FKIsingMedialDart.localMate omega (e, side))] <:+:
      fkIsingSquareExplorationOrder n hn omega := by
  let H := fkIsingSquareLoopGraph n hn omega
  let M := fkIsingSquareLocalSmoothingGraph n omega
  let p : H.Walk (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn omega
  let x : FKIsingSquareMedialCarrier n := .dart (e, side)
  let y : FKIsingSquareMedialCarrier n :=
    .dart (FKIsingMedialDart.localMate omega (e, side))
  rcases fkIsingSquare_localMate_infix_explorationOrder
      n hn omega e side h with hforward | hbackward
  · exact hforward
  · exfalso
    have hy : y ∈ p.support := hbackward.mem (by simp [y])
    have hx : x ∈ p.support := hbackward.mem (by simp [x])
    have hidx := idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareExplorationOrder_nodup n hn omega) hbackward
    change p.support.idxOf x = p.support.idxOf y + 1 at hidx
    have hjlt : p.support.idxOf y < p.length := by
      have hxlt : p.support.idxOf x < p.support.length :=
        List.idxOf_lt_length_iff.mpr hx
      rw [p.length_support, hidx] at hxlt
      omega
    have hgety : p.getVert (p.support.idxOf y) = y :=
      p.getVert_support_idxOf hy
    have hgetx : p.getVert (p.support.idxOf y + 1) = x := by
      have hx' := p.getVert_support_idxOf hx
      rw [hidx] at hx'
      exact hx'
    have hfirst : ¬ M.Adj (p.getVert 0) (p.getVert 1) := by
      intro hlocal
      rcases hlocal with ⟨d, hd, _⟩
      simpa [p] using hd
    have hodd : Odd (p.support.idxOf y) :=
      (isAlternating_path_edge_iff_odd
        (fkIsingSquareLoopGraph_isAlternating_localSmoothing n hn omega)
        p (fkIsingSquareExplorationPath n hn omega).isPath hfirst
        (p.support.idxOf y) hjlt).1 (by
          rw [hgety, hgetx]
          exact ⟨FKIsingMedialDart.localMate omega (e, side), rfl,
            by rw [FKIsingMedialDart.localMate_involutive]⟩)
    have hclass : fkIsingSquareCarrierOddClass n y :=
      by
        rw [← hgety]
        exact (fkIsingSquareExplorationPath_oddClass n hn omega
          (p.support.idxOf y) (Nat.le_of_lt hjlt)).2 hodd
    have hne := fkIsingSquare_localMate_cornerTurn_ne n omega (e, side)
    change (fkIsingSquareSideCorner
      (FKIsingMedialDart.localMate omega (e, side)).2).2 =
        .counterclockwise at hclass
    exact hne (hclass.trans hccw.symm)

theorem fkIsingSquare_open_pathUses_west_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ↔
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setOpen e.1 omega) (e, .west) (.dart (e, .north))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩

theorem fkIsingSquare_open_pathUses_east_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ↔
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setOpen e.1 omega) (e, .east) (.dart (e, .south))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩

theorem fkIsingSquare_closed_pathUses_west_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ↔
      fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .south := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setClosed e.1 omega) (e, .west) (.dart (e, .south))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩

theorem fkIsingSquare_closed_pathUses_east_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ↔
      fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .north := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setClosed e.1 omega) (e, .east) (.dart (e, .north))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩


theorem walkSplice_of_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u v a b c d : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hc : c ∈ p.support) (hd : d ∈ p.support)
    (hab : p.support.idxOf a < p.support.idxOf b)
    (hbc : p.support.idxOf b < p.support.idxOf c)
    (hcd : p.support.idxOf c < p.support.idxOf d) :
    ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v,
      q.IsPath ∧
        q.support = p.support.take (p.support.idxOf a + 1) ++
          p.support.drop (p.support.idxOf d) := by
  let cut : Set (Sym2 V) := {s(a, b), s(c, d)}
  let K := G.deleteEdges cut
  let pa := p.takeUntil a ha
  let pd := p.dropUntil d hd
  have hpa_support : pa.support =
      p.support.take (p.support.idxOf a + 1) := by
    simp [pa, Walk.takeUntil_eq_take,
      Walk.take_support_eq_support_take_succ]
  have hid_le : p.support.idxOf d ≤ p.length := by
    have hid_lt := List.idxOf_lt_length_of_mem hd
    simpa [Walk.length_support] using hid_lt
  have hpd_support : pd.support = p.support.drop (p.support.idxOf d) := by
    simp [pd, Walk.dropUntil_eq_drop,
      Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hid_le]
  have hpa_avoid : ∀ e, e ∈ pa.edges → e ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · have hbpa := pa.snd_mem_support_of_mem_edges hf
      rw [hpa_support, List.mem_take_iff_idxOf_lt hb] at hbpa
      omega
    · have hcpa := pa.fst_mem_support_of_mem_edges hf
      rw [hpa_support, List.mem_take_iff_idxOf_lt hc] at hcpa
      omega
  have hsplit_nodup :
      (p.support.take (p.support.idxOf d) ++
        p.support.drop (p.support.idxOf d)).Nodup := by
    simpa only [List.take_append_drop] using hp.support_nodup
  have hdisj : List.Disjoint (p.support.take (p.support.idxOf d))
      (p.support.drop (p.support.idxOf d)) :=
    hsplit_nodup.disjoint
  have ha_take : a ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt ha]
    omega
  have hc_take : c ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt hc]
    omega
  have hpd_avoid : ∀ e, e ∈ pd.edges → e ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · exact hdisj ha_take (hpd_support ▸ pd.fst_mem_support_of_mem_edges hf)
    · exact hdisj hc_take (hpd_support ▸ pd.fst_mem_support_of_mem_edges hf)
  have hKle : K ≤ medialTwoEdgeSwitch G a b c d := by
    intro x y hxy
    exact Or.inl (Or.inl hxy)
  have hadne : a ≠ d := by
    intro heq
    subst d
    omega
  have had : (medialTwoEdgeSwitch G a b c d).Adj a d := by
    change (((G.deleteEdges {s(a, b), s(c, d)}) ⊔ edge a d) ⊔
      edge c b).Adj a d
    exact Or.inl (Or.inr (by simpa [SimpleGraph.edge_adj] using hadne))
  let paK : K.Walk u a := pa.toDeleteEdges cut hpa_avoid
  let pdK : K.Walk d v := pd.toDeleteEdges cut hpd_avoid
  let pa' := paK.mapLe hKle
  let pd' := pdK.mapLe hKle
  let q := pa'.append (pd'.cons had)
  have hpa'_support : pa'.support = pa.support := by
    rw [Walk.support_mapLe_eq_support]
    apply Walk.support_transfer
  have hpd'_support : pd'.support = pd.support := by
    rw [Walk.support_mapLe_eq_support]
    apply Walk.support_transfer
  have hq_support : q.support =
      p.support.take (p.support.idxOf a + 1) ++
        p.support.drop (p.support.idxOf d) := by
    dsimp only [q]
    rw [Walk.support_append, hpa'_support]
    simp only [Walk.support_cons, List.tail_cons]
    rw [hpd'_support, hpa_support, hpd_support]
  have hai_le : p.support.idxOf a + 1 ≤ p.support.idxOf d := by omega
  have hsub :
      (p.support.take (p.support.idxOf a + 1) ++
        p.support.drop (p.support.idxOf d)).Sublist p.support := by
    simpa [List.dropSlice_eq, Nat.add_sub_of_le hai_le] using
      List.dropSlice_sublist (p.support.idxOf a + 1)
        (p.support.idxOf d - (p.support.idxOf a + 1)) p.support
  refine ⟨q, ?_, hq_support⟩
  rw [Walk.isPath_def, hq_support]
  exact List.Nodup.sublist hsub hp.support_nodup


theorem walkSplice_membership_of_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u v a b c d : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hc : c ∈ p.support) (hd : d ∈ p.support)
    (hab : p.support.idxOf a < p.support.idxOf b)
    (hbc : p.support.idxOf b < p.support.idxOf c)
    (hcd : p.support.idxOf c < p.support.idxOf d) :
    ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v,
      q.IsPath ∧
        q.support = p.support.take (p.support.idxOf a + 1) ++
          p.support.drop (p.support.idxOf d) ∧
        a ∈ q.support ∧ d ∈ q.support ∧
        b ∉ q.support ∧ c ∉ q.support := by
  obtain ⟨q, hq, hq_support⟩ :=
    walkSplice_of_order G p hp ha hb hc hd hab hbc hcd
  have hsplit_nodup :
      (p.support.take (p.support.idxOf d) ++
        p.support.drop (p.support.idxOf d)).Nodup := by
    simpa only [List.take_append_drop] using hp.support_nodup
  have hdisj : List.Disjoint (p.support.take (p.support.idxOf d))
      (p.support.drop (p.support.idxOf d)) :=
    hsplit_nodup.disjoint
  have hb_take_d : b ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt hb]
    omega
  have hc_take_d : c ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt hc]
    omega
  have ha_q : a ∈ q.support := by
    rw [hq_support, List.mem_append]
    exact Or.inl ((List.mem_take_iff_idxOf_lt ha).2 (by omega))
  have hd_drop : d ∈ p.support.drop (p.support.idxOf d) := by
    rw [List.drop_eq_getElem_cons (List.idxOf_lt_length_of_mem hd),
      List.getElem_idxOf (List.idxOf_lt_length_of_mem hd)]
    simp
  have hd_q : d ∈ q.support := by
    rw [hq_support, List.mem_append]
    exact Or.inr hd_drop
  have hb_q : b ∉ q.support := by
    rw [hq_support, List.mem_append]
    rintro (hb_take | hb_drop)
    · rw [List.mem_take_iff_idxOf_lt hb] at hb_take
      omega
    · exact hdisj hb_take_d hb_drop
  have hc_q : c ∉ q.support := by
    rw [hq_support, List.mem_append]
    rintro (hc_take | hc_drop)
    · rw [List.mem_take_iff_idxOf_lt hc] at hc_take
      omega
    · exact hdisj hc_take_d hc_drop
  exact ⟨q, hq, hq_support, ha_q, hd_q, hb_q, hc_q⟩

end
end StatMech.Universality
