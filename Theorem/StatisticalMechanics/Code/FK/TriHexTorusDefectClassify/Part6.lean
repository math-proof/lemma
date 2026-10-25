/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Def.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open StatMech.Lattice

open StatMech.Onsager

theorem triHexTorusDualOfPrimalEdge_of_mem
    (L : ℕ) [Fact (2 < L)] {e : Sym2 (TorusSite L)}
    (he : e ∈ (triangularTorusGraph L).edgeSet) :
    triHexTorusDualOfPrimalEdge L e =
      (triHexTorusDualEdgeEquiv L
        ⟨e, he⟩ : (hexagonalTorusGraph L).edgeSet) := by
  simp [triHexTorusDualOfPrimalEdge, he]


theorem triHexTorusPrimalOfDualOfPrimalEdge
    (L : ℕ) [Fact (2 < L)] {e : Sym2 (TorusSite L)}
    (he : e ∈ (triangularTorusGraph L).edgeSet) :
    triHexTorusPrimalOfDualEdge L
        (triHexTorusDualOfPrimalEdge L e) = e := by
  rw [triHexTorusDualOfPrimalEdge_of_mem L he]
  have hd : ((triHexTorusDualEdgeEquiv L
      ⟨e, he⟩ : (hexagonalTorusGraph L).edgeSet) :
        Sym2 (HexTorusVertex L)) ∈ (hexagonalTorusGraph L).edgeSet :=
    (triHexTorusDualEdgeEquiv L ⟨e, he⟩).2
  simp only [triHexTorusPrimalOfDualEdge, dif_pos hd]
  exact congrArg Subtype.val
    ((triHexTorusDualEdgeEquiv L).symm_apply_apply ⟨e, he⟩)


theorem triHexTorusDualCutGraph_sup_edge
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    {p q : TorusSite L} (hpq : (triangularTorusGraph L).Adj p q) :
    triHexTorusDualCutGraph L (K ⊔ edge p q) =
      (triHexTorusDualCutGraph L K).deleteEdges
        {triHexTorusDualOfPrimalEdge L s(p, q)} := by
  have hep : s(p, q) ∈ (triangularTorusGraph L).edgeSet := by
    simpa only [SimpleGraph.mem_edgeSet] using hpq
  let ep : (triangularTorusGraph L).edgeSet := ⟨s(p, q), hep⟩
  let ed : (hexagonalTorusGraph L).edgeSet :=
    triHexTorusDualEdgeEquiv L ep
  have hed : triHexTorusDualOfPrimalEdge L s(p, q) =
      (ed : Sym2 (HexTorusVertex L)) := by
    simpa [ed, ep] using triHexTorusDualOfPrimalEdge_of_mem L hep
  ext f g
  by_cases hfg : (hexagonalTorusGraph L).Adj f g
  · have hefg : s(f, g) ∈ (hexagonalTorusGraph L).edgeSet := by
      simpa only [SimpleGraph.mem_edgeSet] using hfg
    have hcross : triHexTorusPrimalOfDualEdge L s(f, g) = s(p, q) ↔
        s(f, g) = (ed : Sym2 (HexTorusVertex L)) := by
      simp only [triHexTorusPrimalOfDualEdge, dif_pos hefg]
      constructor
      · intro h
        have hs : (triHexTorusDualEdgeEquiv L).symm
            (⟨s(f, g), hefg⟩ : (hexagonalTorusGraph L).edgeSet) = ep :=
          Subtype.ext h
        have := congrArg (triHexTorusDualEdgeEquiv L) hs
        simpa [ed] using congrArg Subtype.val this
      · intro h
        have hs : (⟨s(f, g), hefg⟩ :
            (hexagonalTorusGraph L).edgeSet) = ed := Subtype.ext h
        have := congrArg (triHexTorusDualEdgeEquiv L).symm hs
        simpa [ep, ed] using congrArg Subtype.val this
    simp only [triHexTorusDualCutGraph_adj, deleteEdges_adj, hfg, true_and,
      Set.mem_singleton_iff]
    rw [hed, edgeSet_sup, edgeSet_edge_of_ne hpq.ne]
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
    exact and_congr_right (fun _ => not_congr hcross)
  · simp [triHexTorusDualCutGraph_adj, deleteEdges_adj, hfg]


theorem triHexTorusCutDualGraph_le_dualCutGraph
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    (S : Set (TorusSite L))
    (hclosed : ∀ {u v}, K.Adj u v → (u ∈ S ↔ v ∈ S)) :
    triHexTorusCutDualGraph L S ≤ triHexTorusDualCutGraph L K := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  let e := triHexTorusPrimalOfDualEdge L s(f, g)
  have hcut : triHexTorusEdgeStraddles S e := hfg.2
  change e ∉ K.edgeSet
  revert hcut
  induction e using Sym2.inductionOn with
  | _ u v =>
      intro hcut hopen
      rw [SimpleGraph.mem_edgeSet] at hopen
      have hs := hclosed hopen
      simp [triHexTorusEdgeStraddles_mk, hs] at hcut


theorem triHexTorusDualCutGraph_crossed_reachable_of_primal_not_reachable
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    {p q : TorusSite L} {f g : HexTorusVertex L}
    (hpq : (triangularTorusGraph L).Adj p q)
    (hmerge : ¬ K.Reachable p q)
    (hdual : triHexTorusDualOfPrimalEdge L s(p, q) = s(f, g)) :
    ((triHexTorusDualCutGraph L K).deleteEdges {s(f, g)}).Reachable f g := by
  classical
  let S : Set (TorusSite L) := {z | K.Reachable p z}
  let B := triHexTorusCutDualGraph L S
  have hclosed : ∀ {u v}, K.Adj u v → (u ∈ S ↔ v ∈ S) := by
    intro u v huv
    change K.Reachable p u ↔ K.Reachable p v
    exact ⟨fun h => h.trans huv.reachable,
      fun h => h.trans huv.symm.reachable⟩
  have hle : B ≤ triHexTorusDualCutGraph L K :=
    triHexTorusCutDualGraph_le_dualCutGraph L K S hclosed
  have hep : s(p, q) ∈ (triangularTorusGraph L).edgeSet := by
    simpa only [SimpleGraph.mem_edgeSet] using hpq
  have hed : s(f, g) ∈ (hexagonalTorusGraph L).edgeSet := by
    rw [← hdual, triHexTorusDualOfPrimalEdge_of_mem L hep]
    exact (triHexTorusDualEdgeEquiv L ⟨s(p, q), hep⟩).2
  have hprimal : triHexTorusPrimalOfDualEdge L s(f, g) = s(p, q) := by
    rw [← hdual]
    exact triHexTorusPrimalOfDualOfPrimalEdge L hep
  have hpS : p ∈ S := SimpleGraph.Reachable.refl p
  have hqS : q ∉ S := hmerge
  have hBadj : B.Adj f g := by
    refine ⟨?_, ?_⟩
    · simpa only [SimpleGraph.mem_edgeSet] using hed
    · rw [hprimal, triHexTorusEdgeStraddles_mk]
      exact iff_of_true hpS hqS
  have hEven : ∀ z, Even (B.degree z) :=
    triHexTorusCutDualGraph_degree_even L S
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even B hEven hBadj
  let c' := c.mapLe hle
  have hcyc' : c'.IsCycle := hcyc.mapLe hle
  have hedge' : s(f, g) ∈ c'.edges := by
    simpa [c', SimpleGraph.Walk.edges_mapLe_eq_edges] using hedge
  exact (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
    (G := triHexTorusDualCutGraph L K)).mpr
      ⟨u, c', hcyc', hedge'⟩ |>.2


theorem triHexTorusFaceCount_sup_edge_le
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    {p q : TorusSite L} (hpq : (triangularTorusGraph L).Adj p q) :
    triHexTorusFaceCount L (K ⊔ edge p q) ≤
      triHexTorusFaceCount L K + 1 := by
  rw [triHexTorusFaceCount_eq_dualCutGraph,
    triHexTorusFaceCount_eq_dualCutGraph,
    triHexTorusDualCutGraph_sup_edge L K hpq]
  exact ecc_deleteEdge_card_le (triHexTorusDualCutGraph L K)
    (triHexTorusDualOfPrimalEdge L s(p, q))


theorem triHexTorusDefect_le_sup_edge_of_reachable
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    {p q : TorusSite L} (hpq : (triangularTorusGraph L).Adj p q)
    (hnew : ¬ K.Adj p q) (hreach : K.Reachable p q) :
    triHexTorusDefect L K ≤ triHexTorusDefect L (K ⊔ edge p q) := by
  have hedge := card_edgeSet_sup_edge K hpq.ne hnew
  have hcomp := card_components_sup_edge_of_reachable K p q hreach
  have hface := triHexTorusFaceCount_sup_edge_le L K hpq
  unfold triHexTorusDefect
  rw [hedge, hcomp]
  push_cast
  omega


theorem triHexTorusFaceCount_sup_edge_of_not_reachable
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    {p q : TorusSite L} (hpq : (triangularTorusGraph L).Adj p q)
    (hmerge : ¬ K.Reachable p q) :
    triHexTorusFaceCount L (K ⊔ edge p q) =
      triHexTorusFaceCount L K := by
  classical
  let D := triHexTorusDualCutGraph L K
  let ed := triHexTorusDualOfPrimalEdge L s(p, q)
  generalize hed : ed = e
  induction e using Sym2.inductionOn with
  | _ f g =>
      have hep : s(p, q) ∈ (triangularTorusGraph L).edgeSet := by
        simpa only [SimpleGraph.mem_edgeSet] using hpq
      have heDual : s(f, g) ∈ (hexagonalTorusGraph L).edgeSet := by
        rw [← hed]
        simp only [ed]
        rw [triHexTorusDualOfPrimalEdge_of_mem L hep]
        exact (triHexTorusDualEdgeEquiv L ⟨s(p, q), hep⟩).2
      have hprimal : triHexTorusPrimalOfDualEdge L s(f, g) = s(p, q) := by
        rw [← hed]
        simp only [ed]
        exact triHexTorusPrimalOfDualOfPrimalEdge L hep
      have heD : D.Adj f g := by
        refine ⟨?_, ?_⟩
        · simpa only [SimpleGraph.mem_edgeSet] using heDual
        · change triHexTorusPrimalOfDualEdge L s(f, g) ∉ K.edgeSet
          rw [hprimal, SimpleGraph.mem_edgeSet]
          exact fun hadj => hmerge hadj.reachable
      have hr : (D.deleteEdges {s(f, g)}).Reachable f g := by
        apply triHexTorusDualCutGraph_crossed_reachable_of_primal_not_reachable
          L K hpq hmerge
        simpa only [ed] using hed
      have hcard := ecc_deleteEdge_card_nonbridge D heD hr
      rw [triHexTorusFaceCount_eq_dualCutGraph,
        triHexTorusFaceCount_eq_dualCutGraph,
        triHexTorusDualCutGraph_sup_edge L K hpq]
      simpa only [D, ed, hed] using hcard


theorem triHexTorusDefect_sup_edge_of_not_reachable
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    {p q : TorusSite L} (hpq : (triangularTorusGraph L).Adj p q)
    (hmerge : ¬ K.Reachable p q) :
    triHexTorusDefect L (K ⊔ edge p q) = triHexTorusDefect L K := by
  have hnew : ¬ K.Adj p q := fun h => hmerge h.reachable
  have hedge := card_edgeSet_sup_edge K hpq.ne hnew
  have hcomp := card_components_sup_edge_of_not_reachable K p q hmerge
  have hface := triHexTorusFaceCount_sup_edge_of_not_reachable L K hpq hmerge
  unfold triHexTorusDefect
  rw [hedge, hface]
  push_cast
  omega


theorem triHexTorusDefect_le_sup_edge
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    {p q : TorusSite L} (hpq : (triangularTorusGraph L).Adj p q)
    (hnew : ¬ K.Adj p q) :
    triHexTorusDefect L K ≤ triHexTorusDefect L (K ⊔ edge p q) := by
  by_cases hreach : K.Reachable p q
  · exact triHexTorusDefect_le_sup_edge_of_reachable
      L K hpq hnew hreach
  · exact (triHexTorusDefect_sup_edge_of_not_reachable
      L K hpq hreach).ge


theorem onsTorusGraph_le_triangularTorusGraph
    (L : ℕ) [Fact (2 < L)] :
    onsTorusGraph L ≤ triangularTorusGraph L := by
  intro u v huv
  rcases huv with (⟨h1, h2 | h2⟩ | ⟨h2, h1 | h1⟩)
  · have huv' : u = v + (0, 1) := by
      ext
      · simpa using h1
      · simpa using h2
    refine ⟨(v, 1), ?_⟩
    change s(v, v + (0, 1)) = s(u, v)
    rw [huv', Sym2.eq_swap]
  · have hvu : v = u + (0, 1) := by
      apply Prod.ext
      · simpa using h1.symm
      · change v.2 = u.2 + 1
        linear_combination -h2
    refine ⟨(u, 1), ?_⟩
    change s(u, u + (0, 1)) = s(u, v)
    rw [hvu]
  · have huv' : u = v + (1, 0) := by
      ext
      · simpa using h1
      · simpa using h2
    refine ⟨(v, 0), ?_⟩
    change s(v, v + (1, 0)) = s(u, v)
    rw [huv', Sym2.eq_swap]
  · have hvu : v = u + (1, 0) := by
      apply Prod.ext
      · change v.1 = u.1 + 1
        linear_combination -h1
      · simpa using h2.symm
    refine ⟨(u, 0), ?_⟩
    change s(u, u + (1, 0)) = s(u, v)
    rw [hvu]


theorem triangularTorusGraph_connected (L : ℕ) [Fact (2 < L)] :
    (triangularTorusGraph L).Connected :=
  (BeffaraDC.onsTorusGraph_connected L).mono
    (onsTorusGraph_le_triangularTorusGraph L)


theorem hexagonalTorusGraph_black_reachable_add_fst
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    (hexagonalTorusGraph L).Reachable (z, false) (z + (1, 0), false) := by
  have h1 : (hexagonalTorusGraph L).Adj
      (z, false) (z + (1, 1), true) := by
    exact ⟨(z, 2), by
      rw [hexagonalTorusIndexedEdge]
      congr 1⟩
  have h2 : (hexagonalTorusGraph L).Adj
      (z + (1, 0), false) (z + (1, 1), true) := by
    exact ⟨(z + (1, 0), 1), by
      rw [hexagonalTorusIndexedEdge]
      congr 1
      ext <;> simp [hexagonalTorusStep]⟩
  exact h1.reachable.trans h2.symm.reachable


theorem hexagonalTorusGraph_black_reachable_add_snd
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    (hexagonalTorusGraph L).Reachable (z, false) (z + (0, 1), false) := by
  have h1 : (hexagonalTorusGraph L).Adj
      (z, false) (z + (1, 1), true) := by
    exact ⟨(z, 2), by
      rw [hexagonalTorusIndexedEdge]
      congr 1⟩
  have h2 : (hexagonalTorusGraph L).Adj
      (z + (0, 1), false) (z + (1, 1), true) := by
    exact ⟨(z + (0, 1), 0), by
      rw [hexagonalTorusIndexedEdge]
      congr 1
      ext <;> simp [hexagonalTorusStep]⟩
  exact h1.reachable.trans h2.symm.reachable


theorem hexagonalTorusGraph_black_reachable_of_ons_adj
    (L : ℕ) [Fact (2 < L)] {u v : TorusSite L}
    (huv : (onsTorusGraph L).Adj u v) :
    (hexagonalTorusGraph L).Reachable (u, false) (v, false) := by
  rcases huv with (⟨h1, h2 | h2⟩ | ⟨h2, h1 | h1⟩)
  · have huv' : u = v + (0, 1) := by
      ext
      · simpa using h1
      · simpa using h2
    simpa [huv'] using
      (hexagonalTorusGraph_black_reachable_add_snd L v).symm
  · have hvu : v = u + (0, 1) := by
      apply Prod.ext
      · simpa using h1.symm
      · change v.2 = u.2 + 1
        linear_combination -h2
    simpa [hvu] using hexagonalTorusGraph_black_reachable_add_snd L u
  · have huv' : u = v + (1, 0) := by
      ext
      · simpa using h1
      · simpa using h2
    simpa [huv'] using
      (hexagonalTorusGraph_black_reachable_add_fst L v).symm
  · have hvu : v = u + (1, 0) := by
      apply Prod.ext
      · change v.1 = u.1 + 1
        linear_combination -h1
      · simpa using h2.symm
    simpa [hvu] using hexagonalTorusGraph_black_reachable_add_fst L u


theorem hexagonalTorusGraph_black_reachable_of_ons_reachable
    (L : ℕ) [Fact (2 < L)] {u v : TorusSite L}
    (huv : (onsTorusGraph L).Reachable u v) :
    (hexagonalTorusGraph L).Reachable (u, false) (v, false) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => rfl
  | tail hxy hyz ih =>
      exact ih.trans
        (hexagonalTorusGraph_black_reachable_of_ons_adj L hyz)


theorem hexagonalTorusGraph_connected (L : ℕ) [Fact (2 < L)] :
    (hexagonalTorusGraph L).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨((0, 0), false), ?_⟩
  rintro ⟨z, b⟩
  cases b with
  | false =>
      exact hexagonalTorusGraph_black_reachable_of_ons_reachable L
        (BeffaraDC.onsTorusGraph_connected L (0, 0) z)
  | true =>
      let a : TorusSite L := z - (1, 0)
      have ha := hexagonalTorusGraph_black_reachable_of_ons_reachable L
        (BeffaraDC.onsTorusGraph_connected L (0, 0) a)
      have hadj : (hexagonalTorusGraph L).Adj (a, false) (z, true) := by
        refine ⟨(a, 0), ?_⟩
        rw [hexagonalTorusIndexedEdge]
        congr 1
        ext <;> simp [a, hexagonalTorusStep]
      exact ha.trans hadj.reachable

@[simp] theorem triHexTorusDualCutGraph_bot
    (L : ℕ) [Fact (2 < L)] :
    triHexTorusDualCutGraph L (⊥ : SimpleGraph (TorusSite L)) =
      hexagonalTorusGraph L := by
  ext f g
  simp [triHexTorusDualCutGraph_adj]

theorem triHexTorusDualCutGraph_full
    (L : ℕ) [Fact (2 < L)] :
    triHexTorusDualCutGraph L (triangularTorusGraph L) = ⊥ := by
  ext f g
  simp only [triHexTorusDualCutGraph_adj, bot_adj, iff_false]
  rintro ⟨hfg, hclosed⟩
  apply hclosed
  have he : s(f, g) ∈ (hexagonalTorusGraph L).edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset] using hfg
  have hp := triHexTorusPrimalOfDualEdge_mem L he
  simpa [SimpleGraph.edgeFinset] using hp

theorem triangularTorusGraph_edge_card
    (L : ℕ) [Fact (2 < L)] :
    (triangularTorusGraph L).edgeFinset.card = 3 * L ^ 2 := by
  rw [SimpleGraph.edgeFinset_card]
  calc
    Fintype.card (triangularTorusGraph L).edgeSet =
        Fintype.card (TriHexTorusEdgeIndex L) :=
      Fintype.card_congr (triangularTorusEdgeChartEquiv L).symm
    _ = 3 * L ^ 2 := by
      simp [TriHexTorusEdgeIndex, TorusSite]
      ring

theorem triHexTorusFaceCount_bot (L : ℕ) [Fact (2 < L)] :
    triHexTorusFaceCount L (⊥ : SimpleGraph (TorusSite L)) = 1 := by
  rw [triHexTorusFaceCount_eq_dualCutGraph, triHexTorusDualCutGraph_bot,
    card_components_eq_one_of_connected (hexagonalTorusGraph_connected L)]

theorem triHexTorusFaceCount_full (L : ℕ) [Fact (2 < L)] :
    triHexTorusFaceCount L (triangularTorusGraph L) = 2 * L ^ 2 := by
  rw [triHexTorusFaceCount_eq_dualCutGraph, triHexTorusDualCutGraph_full,
    card_components_bot, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_prod, ZMod.card]
  rw [Fintype.card_bool]
  ring

@[simp] theorem triHexTorusDefect_bot (L : ℕ) [Fact (2 < L)] :
    triHexTorusDefect L (⊥ : SimpleGraph (TorusSite L)) = 0 := by
  unfold triHexTorusDefect
  rw [triHexTorusFaceCount_bot, card_components_bot,
    Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  simp

theorem triHexTorusDefect_full (L : ℕ) [Fact (2 < L)] :
    triHexTorusDefect L (triangularTorusGraph L) = 2 := by
  have hedge : (triangularTorusGraph L).edgeSet.ncard = 3 * L ^ 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact triangularTorusGraph_edge_card L
  unfold triHexTorusDefect
  rw [hedge,
    card_components_eq_one_of_connected (triangularTorusGraph_connected L),
    triHexTorusFaceCount_full, Nat.card_eq_fintype_card,
    Fintype.card_prod, ZMod.card]
  push_cast
  ring


theorem triHexTorusDefect_nonnegative
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    (hK : K ≤ triangularTorusGraph L) :
    0 ≤ triHexTorusDefect L K := by
  classical
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz
        have hempty : K.edgeSet = ∅ :=
          (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
        have hbot : K = ⊥ := by
          rw [← SimpleGraph.edgeSet_eq_empty]
          exact hempty
        subst K
        rw [triHexTorusDefect_bot]
      · have hne : K.edgeSet.Nonempty := by
          rw [← Set.ncard_pos (Set.toFinite _), hn]
          exact hpos
        obtain ⟨e, he⟩ := hne
        obtain ⟨p, q⟩ := e
        let K' := K.deleteEdges {s(p, q)}
        have hKeq : K = K' ⊔ edge p q :=
          deleteEdges_sup_edge_eq K p q he
        have hdrop : K'.edgeSet.ncard + 1 = K.edgeSet.ncard :=
          card_edgeSet_deleteEdges_add_one K p q he
        have hn' : K'.edgeSet.ncard = n - 1 := by omega
        have hK' : K' ≤ triangularTorusGraph L :=
          le_trans (SimpleGraph.deleteEdges_le _) hK
        have ihK' : 0 ≤ triHexTorusDefect L K' :=
          ih (n - 1) (by omega) K' hK' hn'
        have hpqK : K.Adj p q := by
          simpa only [SimpleGraph.mem_edgeSet] using he
        have hpq : (triangularTorusGraph L).Adj p q := hK hpqK
        have hnew : ¬ K'.Adj p q := by
          rw [SimpleGraph.deleteEdges_adj]
          simp
        have hstep := triHexTorusDefect_le_sup_edge L K' hpq hnew
        rw [← hKeq] at hstep
        exact ihK'.trans hstep


theorem triHexTorusDefect_le_two
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    (hK : K ≤ triangularTorusGraph L) :
    triHexTorusDefect L K ≤ 2 := by
  classical
  let A := triangularTorusGraph L
  let M : Set (Sym2 (TorusSite L)) := A.edgeSet \ K.edgeSet
  generalize hn : M.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz
        have hMempty : M = ∅ :=
          (Set.ncard_eq_zero (Set.toFinite M)).mp hn
        have hAK : A ≤ K := by
          intro p q hpq
          by_contra hnot
          have he : s(p, q) ∈ M := by
            exact ⟨by simpa only [SimpleGraph.mem_edgeSet] using hpq,
              by simpa only [SimpleGraph.mem_edgeSet] using hnot⟩
          rw [hMempty] at he
          exact he
        have hKA : K = A := le_antisymm hK hAK
        subst K
        exact (triHexTorusDefect_full L).le
      · have hMne : M.Nonempty := by
          rw [← Set.ncard_pos (Set.toFinite _), hn]
          exact hpos
        obtain ⟨e, heA, heK⟩ := hMne
        obtain ⟨p, q⟩ := e
        have hpq : A.Adj p q := by
          simpa only [SimpleGraph.mem_edgeSet] using heA
        have hnew : ¬ K.Adj p q := by
          simpa only [SimpleGraph.mem_edgeSet] using heK
        let K' := K ⊔ edge p q
        have hK' : K' ≤ A := by
          exact sup_le hK ((edge_le_iff (G := A)).2 (Or.inr hpq))
        have hMset : A.edgeSet \ K'.edgeSet = M \ {s(p, q)} := by
          ext e'
          simp only [K', M, edgeSet_sup, edgeSet_edge_of_ne hpq.ne,
            Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
          tauto
        have hdrop : (M \ {s(p, q)}).ncard + 1 = M.ncard :=
          Set.ncard_diff_singleton_add_one ⟨heA, heK⟩ (Set.toFinite M)
        have hn' : (A.edgeSet \ K'.edgeSet).ncard = n - 1 := by
          rw [hMset]
          omega
        have ihK' : triHexTorusDefect L K' ≤ 2 := by
          exact ih (n - 1) (by omega) K' hK' hn'
        have hstep := triHexTorusDefect_le_sup_edge L K hpq hnew
        exact hstep.trans ihK'


theorem triHexTorusDefect_classified
    (L : ℕ) [Fact (2 < L)] (K : SimpleGraph (TorusSite L))
    (hK : K ≤ triangularTorusGraph L) :
    triHexTorusDefect L K = 0 ∨ triHexTorusDefect L K = 1 ∨
      triHexTorusDefect L K = 2 := by
  have h0 := triHexTorusDefect_nonnegative L K hK
  have h2 := triHexTorusDefect_le_two L K hK
  omega


theorem triHexTorusDefect_openSub_classified
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L))) :
    triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) = 0 ∨
      triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) = 1 ∨
        triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) = 2 :=
  triHexTorusDefect_classified L _
    (FK.openSub_le (triangularTorusGraph L) omega)

end PeriodicPlanar
end FK
end StatMech
