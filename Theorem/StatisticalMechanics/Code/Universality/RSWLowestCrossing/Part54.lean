/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part53
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightPathBelow_irrefl {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : ¬ rlc_rightPathBelow gamma gamma := by
  rintro (h | h)
  · exact (Finset.ssubset_iff_subset_ne.mp h).2 rfl
  · exact (lt_irrefl _ h.2)

theorem rlc_leftPathAbove_irrefl {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : ¬ rlc_leftPathAbove gamma gamma := by
  rintro (h | h)
  · exact (Finset.ssubset_iff_subset_ne.mp h).2 rfl
  · exact (lt_irrefl _ h.2)

theorem rlc_rightPathBelow_rank_lt {n : ℤ}
    {delta gamma : RlcRightDiagonalPath n}
    (h : rlc_rightPathBelow delta gamma) :
    rlc_rightPathRank delta < rlc_rightPathRank gamma := by
  let N := Fintype.card (RlcRightDiagonalPath n)
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨gamma⟩
  have hindex : rlc_rightPathIndex delta < N :=
    (Fintype.equivFin (RlcRightDiagonalPath n) delta).isLt
  rcases h with hstrict | heq
  · have hcard : (rlc_rightExploredVertices delta).card <
        (rlc_rightExploredVertices gamma).card :=
      Finset.card_lt_card hstrict
    have hmul : (rlc_rightExploredVertices delta).card * N + N ≤
        (rlc_rightExploredVertices gamma).card * N := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hcard)
    dsimp only [rlc_rightPathRank]
    change _ * N + rlc_rightPathIndex delta <
      _ * N + rlc_rightPathIndex gamma
    calc
      _ * N + rlc_rightPathIndex delta < _ * N + N :=
        Nat.add_lt_add_left hindex _
      _ ≤ _ * N := hmul
      _ ≤ _ * N + rlc_rightPathIndex gamma := Nat.le_add_right _ _
  · dsimp only [rlc_rightPathRank]
    rw [heq.1]
    exact Nat.add_lt_add_left heq.2 _

theorem rlc_leftPathAbove_rank_lt {n : ℤ}
    {delta gamma : RlcLeftDiagonalPath n}
    (h : rlc_leftPathAbove delta gamma) :
    rlc_leftPathRank delta < rlc_leftPathRank gamma := by
  let N := Fintype.card (RlcLeftDiagonalPath n)
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨gamma⟩
  have hindex : rlc_leftPathIndex delta < N :=
    (Fintype.equivFin (RlcLeftDiagonalPath n) delta).isLt
  rcases h with hstrict | heq
  · have hcard : (rlc_leftExploredVertices delta).card <
        (rlc_leftExploredVertices gamma).card :=
      Finset.card_lt_card hstrict
    have hmul : (rlc_leftExploredVertices delta).card * N + N ≤
        (rlc_leftExploredVertices gamma).card * N := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hcard)
    dsimp only [rlc_leftPathRank]
    change _ * N + rlc_leftPathIndex delta <
      _ * N + rlc_leftPathIndex gamma
    calc
      _ * N + rlc_leftPathIndex delta < _ * N + N :=
        Nat.add_lt_add_left hindex _
      _ ≤ _ * N := hmul
      _ ≤ _ * N + rlc_leftPathIndex gamma := Nat.le_add_right _ _
  · dsimp only [rlc_leftPathRank]
    rw [heq.1]
    exact Nat.add_lt_add_left heq.2 _

theorem rlc_pathEdge_endpoints_mem_vertices {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) {x y : Site 2}
    (he : s(x, y) ∈ rlc_pathEdges gamma) :
    x ∈ rlc_pathVertices gamma ∧ y ∈ rlc_pathVertices gamma := by
  simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
  obtain ⟨e, he, heq⟩ := he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have heq' : s(x, y) = s((u : Site 2), (v : Site 2)) := by
      simpa using heq.symm
    rw [Sym2.eq_iff] at heq'
    rcases heq' with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
    · subst x; subst y
      constructor
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u, gamma.2.2.1.fst_mem_support_of_mem_edges he, rfl⟩
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨v, gamma.2.2.1.snd_mem_support_of_mem_edges he, rfl⟩
    · subst x; subst y
      constructor
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨v, gamma.2.2.1.snd_mem_support_of_mem_edges he, rfl⟩
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u, gamma.2.2.1.fst_mem_support_of_mem_edges he, rfl⟩


theorem rlc_pathVertex_mem_rect {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma) : z ∈ rect a b c d := by
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact u.2


theorem rlc_rightSide_strictTop_height_gt {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (z : rightSide 0 (2 * n) (-n) n)
    (hzTop : (z : Site 2) ∈ rlc_strictTopSet gamma) :
    (gamma.1.2.1 : Site 2) 1 < (z : Site 2) 1 := by
  classical
  by_contra hnot
  have hzle : (z : Site 2) 1 ≤ (gamma.1.2.1 : Site 2) 1 :=
    le_of_not_gt hnot
  have hEndPath : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hzNeEnd : (z : Site 2) ≠ (gamma.1.2.1 : Site 2) := by
    intro h
    exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path gamma))
      hzTop (h ▸ hEndPath)
  have hlt : (z : Site 2) 1 < (gamma.1.2.1 : Site 2) 1 := by
    apply lt_of_le_of_ne hzle
    intro h
    apply hzNeEnd
    funext i
    fin_cases i
    · exact z.2.2.trans gamma.1.2.1.2.2.symm
    · exact h
  obtain ⟨x0, hxTop, hxPath, hreach⟩ := hzTop
  let x : topSide 0 (2 * n) (-n) n := ⟨x0, hxTop⟩
  obtain ⟨wAvoid⟩ := hreach
  let hle : rlc_rightPathAvoidGraph gamma ≤ hypercubicLattice 2 :=
    fun _ _ h => h.1
  let W : (hypercubicLattice 2).Walk (x : Site 2) (z : Site 2) :=
    wAvoid.mapLe hle
  have hWbox : ∀ q ∈ W.support,
      q ∈ rect 0 (2 * n) (-n) n := by
    intro q hq
    have hq' : q ∈ wAvoid.support := by
      simpa [W, SimpleGraph.Walk.support_mapLe_eq_support] using hq
    exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxPath
      (wAvoid.takeUntil q hq')).1
  have hWavoid : ∀ q ∈ W.support,
      q ∉ rlc_pathVertices gamma.1 := by
    intro q hq
    have hq' : q ∈ wAvoid.support := by
      simpa [W, SimpleGraph.Walk.support_mapLe_eq_support] using hq
    exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxPath
      (wAvoid.takeUntil q hq')).2
  have hEndNotW : (gamma.1.2.1 : Site 2) ∉ W.support := by
    intro h
    exact (hWavoid _ h) hEndPath
  let R := rlc_cornerReturn x z
  let C : (hypercubicLattice 2).Walk (x : Site 2) (x : Site 2) :=
    W.append R
  have hRayReturn (p : Site 2)
      (hp : p ∈ rect 0 (2 * n) (-n) n) :
      jec_rayCount p R = 0 := by
    exact rlc_cornerReturn_rayCount_zero x z p hp
  have hStartRect : (gamma.1.1 : Site 2) ∈
      rect 0 (2 * n) (-n) n := leftSide_subset gamma.1.1.2
  have hEndRect : (gamma.1.2.1 : Site 2) ∈
      rect 0 (2 * n) (-n) n := rightSide_subset gamma.1.2.1.2
  have hRayStartW : jec_rayCount (gamma.1.1 : Site 2) W = 0 := by
    apply jec_rayCount_eq_zero_of_right
    intro q hq
    have hqR := hWbox q hq
    have hstartSide := gamma.1.1.2
    rw [mem_leftSide] at hstartSide
    rw [mem_rect] at hqR
    simpa [hstartSide.2] using hqR.1
  have hRayStart : Even (jec_rayCount (gamma.1.1 : Site 2) C) := by
    rw [show jec_rayCount (gamma.1.1 : Site 2) C =
      jec_rayCount (gamma.1.1 : Site 2) W +
        jec_rayCount (gamma.1.1 : Site 2) R by
          exact jec_rayCount_append _ W R,
      hRayStartW, hRayReturn _ hStartRect]
    exact Even.zero
  let y : rightSide 0 (2 * n) (-n) n := gamma.1.2.1
  have hRayEndEq : jec_rayCount (y : Site 2) W =
      crossCount (jec_belowSet ((y : Site 2) 1)) W :=
    rlc_ray_eq_below_right_of_avoids y W hWbox hEndNotW
  have hCrossOdd : ¬ Even
      (crossCount (jec_belowSet ((y : Site 2) 1)) W) := by
    rw [crossCount_parity]
    simp only [jec_mem_belowSet]
    have hx1 : (x : Site 2) 1 = n := x.2.2
    have hy1le : (y : Site 2) 1 ≤ n := by
      have hySide := y.2
      rw [mem_rightSide, mem_rect] at hySide
      exact hySide.1.2.2.2
    have hxNot : ¬ (x : Site 2) 1 ≤ (y : Site 2) 1 - 1 := by
      omega
    have hzIn : (z : Site 2) 1 ≤ (y : Site 2) 1 - 1 := by
      dsimp only [y]
      omega
    exact fun hiff => hxNot (hiff.mpr hzIn)
  have hRayEnd : ¬ Even (jec_rayCount (y : Site 2) C) := by
    rw [show jec_rayCount (y : Site 2) C =
      jec_rayCount (y : Site 2) W + jec_rayCount (y : Site 2) R by
        exact jec_rayCount_append _ W R,
      hRayEndEq, hRayReturn _ hEndRect, add_zero]
    exact hCrossOdd
  let hom : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)) →g hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect 0 (2 * n) (-n) n)).toHom
  let gW : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2) :=
    gamma.1.2.2.1.map hom
  obtain ⟨q, hqGammaRev, hqC⟩ :=
    ccs_closedLoop_separatingSide_forces_cross C
      ({(y : Site 2)} : Set (Site 2))
      ({(gamma.1.1 : Site 2)} : Set (Site 2))
      (by
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst q
        exact hRayEnd)
      (by
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst q
        exact hRayStart)
      (by simp [y]) (by simp) gW.reverse
  have hqGamma : q ∈ gW.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hqGammaRev
  have hqPath : q ∈ rlc_pathVertices gamma.1 := by
    dsimp only [gW] at hqGamma
    have hqMapped : q ∈ List.map hom gamma.1.2.2.1.support := by
      have hsupp := SimpleGraph.Walk.support_map hom gamma.1.2.2.1
      have hm := congrArg (fun l => q ∈ l) hsupp
      exact Eq.mp hm hqGamma
    rw [List.mem_map] at hqMapped
    obtain ⟨u, hu, huq⟩ := hqMapped
    change (u : Site 2) = q at huq
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨u, hu, huq⟩
  have hqRect := rlc_pathVertex_mem_rect gamma.1 hqPath
  dsimp only [C] at hqC
  rw [SimpleGraph.Walk.mem_support_append_iff] at hqC
  rcases hqC with hqW | hqR
  · exact (hWavoid q hqW) hqPath
  · rcases rlc_cornerReturn_support_inside x z hqR hqRect with hqz | hqx
    · exact (hWavoid _ W.end_mem_support) (hqz ▸ hqPath)
    · apply hxPath
      have hxPath' : (x : Site 2) ∈ rlc_pathVertices gamma.1 :=
        hqx ▸ hqPath
      simpa [x] using hxPath'


theorem rlc_right_endpoints_not_both_unsafe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    ¬ ((gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧
      (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) := by
  rintro ⟨hgamma, hdelta⟩
  have hgammaPath : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hdeltaPath : (delta.1.2.1 : Site 2) ∈
      rlc_pathVertices delta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩,
      delta.1.2.2.1.end_mem_support, rfl⟩
  have hgammaTopDelta : (gamma.1.2.1 : Site 2) ∈
      rlc_strictTopSet delta := by
    rcases hgamma with hgammaTop | hgammaTop
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) hgammaTop hgammaPath)
    · exact hgammaTop
  have hdeltaTopGamma : (delta.1.2.1 : Site 2) ∈
      rlc_strictTopSet gamma := by
    rcases hdelta with hdeltaTop | hdeltaTop
    · exact hdeltaTop
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) hdeltaTop hdeltaPath)
  have hgd := rlc_rightSide_strictTop_height_gt hn delta
    gamma.1.2.1 hgammaTopDelta
  have hdg := rlc_rightSide_strictTop_height_gt hn gamma
    delta.1.2.1 hdeltaTopGamma
  omega


theorem rlc_exists_safe_right_endpoint {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    (gamma.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∨
      (delta.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  by_contra h
  push_neg at h
  exact rlc_right_endpoints_not_both_unsafe hn gamma delta h


theorem rlc_pathEdge_lattice {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) {x y : Site 2}
    (he : s(x, y) ∈ rlc_pathEdges gamma) :
    (hypercubicLattice 2).Adj x y := by
  simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
  obtain ⟨e, he, heq⟩ := he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj := gamma.2.2.1.adj_of_mem_edges he
      have heq' : s(x, y) = s((u : Site 2), (v : Site 2)) := by
        simpa using heq.symm
      rw [Sym2.eq_iff] at heq'
      rcases heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm


theorem rlc_walk_pred_constant {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (P : V → Prop)
    (hstep : ∀ {u v : V}, s(u, v) ∈ p.edges → (P u ↔ P v))
    {z : V} (hz : z ∈ p.support) : P z ↔ P a := by
  induction p with
  | nil =>
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ Iff.rfl
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Iff.rfl
      · have htail : ∀ {u v : V}, s(u, v) ∈ p.edges → (P u ↔ P v) := by
          intro u v he
          apply hstep
          simpa using Or.inr he
        exact (ih htail hz).trans (hstep (by simp)).symm


theorem rlc_strictTopSet_mem_iff_walk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {a b : Site 2}
    (p : (hypercubicLattice 2).Walk a b)
    (hbox : ∀ z ∈ p.support, z ∈ rect 0 (2 * n) (-n) n)
    (havoid : ∀ z ∈ p.support, z ∉ rlc_pathVertices gamma.1)
    {z : Site 2} (hz : z ∈ p.support) :
    z ∈ rlc_strictTopSet gamma ↔ a ∈ rlc_strictTopSet gamma := by
  apply rlc_walk_pred_constant p (fun u => u ∈ rlc_strictTopSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huTop
      exact rlc_strictTopSet_step gamma huTop (hbox v hv) (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvTop
      exact rlc_strictTopSet_step gamma hvTop (hbox u hu) (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz


theorem rlc_strictBelowSet_mem_iff_walk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {a b : Site 2}
    (p : (hypercubicLattice 2).Walk a b)
    (hbox : ∀ z ∈ p.support, z ∈ rect 0 (2 * n) (-n) n)
    (havoid : ∀ z ∈ p.support, z ∉ rlc_pathVertices gamma.1)
    {z : Site 2} (hz : z ∈ p.support) :
    z ∈ rlc_strictBelowSet gamma ↔ a ∈ rlc_strictBelowSet gamma := by
  apply rlc_walk_pred_constant p (fun u => u ∈ rlc_strictBelowSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huBelow
      exact rlc_strictBelowSet_step gamma huBelow (hbox v hv) (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvBelow
      exact rlc_strictBelowSet_step gamma hvBelow (hbox u hu) (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz


theorem rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n)
    {a b : rect 0 (2 * n) (-n) n}
    (p : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk a b)
    (havoid : ∀ z ∈ p.support,
      (z : Site 2) ∉ rlc_pathVertices gamma.1)
    {z : rect 0 (2 * n) (-n) n} (hz : z ∈ p.support) :
    (z : Site 2) ∈ rlc_strictTopSet gamma ↔
      (a : Site 2) ∈ rlc_strictTopSet gamma := by
  apply rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictTopSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huTop
      exact rlc_strictTopSet_step gamma huTop v.2 (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvTop
      exact rlc_strictTopSet_step gamma hvTop u.2 (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz


theorem rlc_strictBelowSet_mem_iff_rectWalk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n)
    {a b : rect 0 (2 * n) (-n) n}
    (p : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk a b)
    (havoid : ∀ z ∈ p.support,
      (z : Site 2) ∉ rlc_pathVertices gamma.1)
    {z : rect 0 (2 * n) (-n) n} (hz : z ∈ p.support) :
    (z : Site 2) ∈ rlc_strictBelowSet gamma ↔
      (a : Site 2) ∈ rlc_strictBelowSet gamma := by
  apply rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictBelowSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huBelow
      exact rlc_strictBelowSet_step gamma huBelow v.2 (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvBelow
      exact rlc_strictBelowSet_step gamma hvBelow u.2 (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz


theorem rlc_strictTopSet_mem_iff_path_start_of_disjoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    {z : Site 2} (hz : z ∈ rlc_pathVertices delta.1) :
    z ∈ rlc_strictTopSet gamma ↔
      (delta.1.1 : Site 2) ∈ rlc_strictTopSet gamma := by
  classical
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨zs, hzs, rfl⟩ := hz
  let p := delta.1.2.2.1
  have hconst := rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictTopSet gamma) (z := zs) ?_ hzs
  · simpa [p] using hconst
  · intro u v he
    have heAmb : s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges delta.1 := by
      simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
      exact ⟨s(u, v), he, by simp⟩
    have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heAmb
    have huNot : (u : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hu => (Finset.disjoint_left.mp hdisj) hu hends.1
    have hvNot : (v : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hv => (Finset.disjoint_left.mp hdisj) hv hends.2
    constructor
    · intro huTop
      exact rlc_strictTopSet_step gamma huTop v.2 hvNot
        (rlc_pathEdge_lattice delta.1 heAmb)
    · intro hvTop
      exact rlc_strictTopSet_step gamma hvTop u.2 huNot
        (rlc_pathEdge_lattice delta.1 heAmb).symm

theorem rlc_strictBottomSet_mem_iff_path_start_of_disjoint {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    {z : Site 2} (hz : z ∈ rlc_pathVertices delta.1) :
    z ∈ rlc_strictBottomSet gamma ↔
      (delta.1.1 : Site 2) ∈ rlc_strictBottomSet gamma := by
  classical
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨zs, hzs, rfl⟩ := hz
  let p := delta.1.2.2.1
  have hconst := rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictBottomSet gamma) (z := zs) ?_ hzs
  · simpa [p] using hconst
  · intro u v he
    have heAmb : s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges delta.1 := by
      simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
      exact ⟨s(u, v), he, by simp⟩
    have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heAmb
    have huNot : (u : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hu => (Finset.disjoint_left.mp hdisj) hu hends.1
    have hvNot : (v : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hv => (Finset.disjoint_left.mp hdisj) hv hends.2
    constructor
    · intro huBottom
      exact rlc_strictBottomSet_step gamma huBottom v.2 hvNot
        (rlc_pathEdge_lattice delta.1 heAmb)
    · intro hvBottom
      exact rlc_strictBottomSet_step gamma hvBottom u.2 huNot
        (rlc_pathEdge_lattice delta.1 heAmb).symm


theorem rlc_rightPathEdge_enter_strictTop_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∉ rlc_strictTopSet delta)
    (hv : v ∈ rlc_strictTopSet delta) :
    u ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictTopSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_false hu (not_not.mpr hv)
  rcases rlc_strictTopSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact huDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path delta)) hv hvDelta)


theorem rlc_rightPathEdge_exit_strictTop_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∈ rlc_strictTopSet delta)
    (hv : v ∉ rlc_strictTopSet delta) :
    v ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictTopSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_true hu hv
  rcases rlc_strictTopSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path delta)) hu huDelta)
  · exact hvDelta

theorem rlc_leftPathEdge_enter_strictBottom_common {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∉ rlc_strictBottomSet delta)
    (hv : v ∈ rlc_strictBottomSet delta) :
    u ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictBottomSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_false hu (not_not.mpr hv)
  rcases rlc_strictBottomSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact huDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictBottomSet_disjoint_path delta)) hv hvDelta)

theorem rlc_leftPathEdge_exit_strictBottom_common {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∈ rlc_strictBottomSet delta)
    (hv : v ∉ rlc_strictBottomSet delta) :
    v ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictBottomSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_true hu hv
  rcases rlc_strictBottomSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictBottomSet_disjoint_path delta)) hu huDelta)
  · exact hvDelta


end Universality
end StatMech
