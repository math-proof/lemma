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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part72
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightSafeTraceReachability_of_frontierPathProperty {n : ℤ}
    (hfrontier : RlcRightFrontierPathProperty n) :
    RlcRightSafeTraceReachability n := by
  intro gamma delta
  obtain ⟨lambda, hedges, hsafe⟩ := hfrontier gamma delta
  exact rlc_rightSafeTraceReachable_of_path_safe
    gamma delta lambda hedges hsafe


theorem rlc_rightFrontierPathProperty_of_safeTraceReachability {n : ℤ}
    (hsafe : RlcRightSafeTraceReachability n) :
    RlcRightFrontierPathProperty n := by
  classical
  intro gamma delta
  obtain ⟨x, y, hxHalf, hyHalf, hxSafe, _hySafe, hreach⟩ :=
    hsafe gamma delta
  let q := hreach.some.toPath
  have hle : rlc_rightSafeTraceGraph gamma delta ≤
      (hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n) :=
    fun _ _ h => h.1
  let qRect : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk
      ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ :=
    q.1.mapLe hle
  have hqRect : qRect.IsPath := by
    exact (SimpleGraph.Walk.mapLe_isPath hle).mpr q.2
  let lambda0 : RlcCrossingPath 0 (2 * n) (-n) n :=
    ⟨x, y, ⟨qRect, hqRect⟩⟩
  let lambda : RlcRightDiagonalPath n :=
    ⟨lambda0, hxHalf, hyHalf⟩
  refine ⟨lambda, ?_, ?_⟩
  · intro e he
    simp only [rlc_pathEdges, lambda, lambda0, Finset.mem_image,
      List.mem_toFinset] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have heq : e0 ∈ q.1.edges := by
      rw [← rlc_edges_mapLe_eq hle q.1]
      exact he0
    induction e0 using Sym2.inductionOn with
    | _ u v =>
        exact (q.1.adj_of_mem_edges heq).2.1
  · rw [Set.disjoint_left]
    intro z hzUpper hzPath
    change z ∈ qRect.support.toFinset.image Subtype.val at hzPath
    rw [Finset.mem_image] at hzPath
    obtain ⟨u, hu, huz⟩ := hzPath
    have hu' : u ∈ qRect.support := by simpa using hu
    have huq : u ∈ q.1.support := by
      simpa [qRect, SimpleGraph.Walk.support_mapLe_eq_support] using hu'
    have huSafe := rlc_rightSafeTraceGraph_walk_support_safe
      gamma delta q.1 hxSafe huq
    exact huSafe (huz ▸ hzUpper)

theorem rlc_rightSafeTraceReachability_iff_frontierPathProperty {n : ℤ} :
    RlcRightSafeTraceReachability n ↔ RlcRightFrontierPathProperty n := by
  constructor
  · exact rlc_rightFrontierPathProperty_of_safeTraceReachability
  · exact rlc_rightSafeTraceReachability_of_frontierPathProperty

theorem rlc_leftFrontierPathProperty_of_safeTraceReachability {n : ℤ}
    (hsafe : RlcLeftSafeTraceReachability n) :
    RlcLeftFrontierPathProperty n := by
  classical
  intro gamma delta
  obtain ⟨x, y, hxHalf, hyHalf, hxSafe, _hySafe, hreach⟩ :=
    hsafe gamma delta
  let q := hreach.some.toPath
  have hle : rlc_leftSafeTraceGraph gamma delta ≤
      (hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n) :=
    fun _ _ h => h.1
  let qRect : ((hypercubicLattice 2).induce
      (rect (-2 * n) 0 (-n) n)).Walk
      ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ :=
    q.1.mapLe hle
  have hqRect : qRect.IsPath := by
    exact (SimpleGraph.Walk.mapLe_isPath hle).mpr q.2
  let lambda0 : RlcCrossingPath (-2 * n) 0 (-n) n :=
    ⟨x, y, ⟨qRect, hqRect⟩⟩
  let lambda : RlcLeftDiagonalPath n :=
    ⟨lambda0, hxHalf, hyHalf⟩
  refine ⟨lambda, ?_, ?_⟩
  · intro e he
    simp only [rlc_pathEdges, lambda, lambda0, Finset.mem_image,
      List.mem_toFinset] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have heq : e0 ∈ q.1.edges := by
      rw [← rlc_edges_mapLe_eq hle q.1]
      exact he0
    induction e0 using Sym2.inductionOn with
    | _ u v =>
        exact (q.1.adj_of_mem_edges heq).2.1
  · rw [Set.disjoint_left]
    intro z hzLower hzPath
    change z ∈ qRect.support.toFinset.image Subtype.val at hzPath
    rw [Finset.mem_image] at hzPath
    obtain ⟨u, hu, huz⟩ := hzPath
    have hu' : u ∈ qRect.support := by simpa using hu
    have huq : u ∈ q.1.support := by
      simpa [qRect, SimpleGraph.Walk.support_mapLe_eq_support] using hu'
    have huSafe := rlc_leftSafeTraceGraph_walk_support_safe
      gamma delta q.1 hxSafe huq
    exact huSafe (huz ▸ hzLower)

theorem rlc_leftFrontierPathProperty_of_right {n : ℤ}
    (hright : RlcRightFrontierPathProperty n) :
    RlcLeftFrontierPathProperty n := by
  classical
  intro gamma delta
  let gammaR := rlc_rot180LeftPath gamma
  let deltaR := rlc_rot180LeftPath delta
  obtain ⟨lambdaR, hedges, hdisj⟩ := hright gammaR deltaR
  let lambda := rlc_rot180RightPath lambdaR
  refine ⟨lambda, ?_, ?_⟩
  · dsimp only [lambda]
    rw [rlc_pathEdges_rot180RightPath]
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
    have heInput := hedges he0
    rw [Finset.mem_union] at heInput
    rcases heInput with heGamma | heDelta
    · dsimp only [gammaR] at heGamma
      rw [rlc_pathEdges_rot180LeftPath] at heGamma
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp heGamma
      have hback := congrArg (Sym2.map rlc_rot180) hae
      have : Sym2.map rlc_rot180 e0 = a := by simpa using hback.symm
      exact Finset.mem_union_left _ (this ▸ ha)
    · dsimp only [deltaR] at heDelta
      rw [rlc_pathEdges_rot180LeftPath] at heDelta
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp heDelta
      have hback := congrArg (Sym2.map rlc_rot180) hae
      have : Sym2.map rlc_rot180 e0 = a := by simpa using hback.symm
      exact Finset.mem_union_right _ (this ▸ ha)
  · rw [Set.disjoint_left]
    intro z hzLower hzPath
    dsimp only [lambda] at hzPath
    rw [rlc_pathVertices_rot180RightPath] at hzPath
    change z ∈ (rlc_pathVertices lambdaR.1).image rlc_rot180 at hzPath
    rw [Finset.mem_image] at hzPath
    obtain ⟨a, ha, haz⟩ := hzPath
    have hza : rlc_rot180 z = a := by
      apply rlc_rot180.injective
      simpa using haz.symm
    apply (Set.disjoint_left.mp hdisj) ?_ (hza ▸ ha)
    rcases hzLower with hzGamma | hzDelta
    · left
      change rlc_rot180 z ∈ rlc_strictTopSet gammaR
      exact (rlc_rot180_mem_strictTop_iff_mem_strictBottom gamma z).mpr hzGamma
    · right
      change rlc_rot180 z ∈ rlc_strictTopSet deltaR
      exact (rlc_rot180_mem_strictTop_iff_mem_strictBottom delta z).mpr hzDelta

theorem rlc_rightEnvelopeProperty_of_frontierPath {n : ℤ}
    (hfrontier : RlcRightFrontierPathProperty n) :
    RlcRightEnvelopeProperty n := by
  intro gamma delta
  obtain ⟨lambda, hedges, hdisj⟩ := hfrontier gamma delta
  refine ⟨lambda, hedges, ?_⟩
  have hdisjGamma : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inl hz) hzp
  have hdisjDelta : Disjoint (rlc_strictTopSet delta)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inr hz) hzp
  have htopGamma : rlc_strictTopSet gamma ⊆ rlc_strictTopSet lambda :=
    rlc_strictTopSet_mono_of_disjoint_path gamma lambda hdisjGamma
  have htopDelta : rlc_strictTopSet delta ⊆ rlc_strictTopSet lambda :=
    rlc_strictTopSet_mono_of_disjoint_path delta lambda hdisjDelta
  intro z hz
  rw [Finset.mem_inter]
  rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hz
  constructor
  · rw [rlc_rightExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzTop
    exact hz.2 (by
      simpa using htopGamma (by simpa using hzTop))
  · rw [rlc_rightExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzTop
    exact hz.2 (by
      simpa using htopDelta (by simpa using hzTop))

theorem rlc_leftEnvelopeProperty_of_frontierPath {n : ℤ}
    (hfrontier : RlcLeftFrontierPathProperty n) :
    RlcLeftEnvelopeProperty n := by
  intro gamma delta
  obtain ⟨lambda, hedges, hdisj⟩ := hfrontier gamma delta
  refine ⟨lambda, hedges, ?_⟩
  have hdisjGamma : Disjoint (rlc_strictBottomSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inl hz) hzp
  have hdisjDelta : Disjoint (rlc_strictBottomSet delta)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inr hz) hzp
  have hbottomGamma : rlc_strictBottomSet gamma ⊆
      rlc_strictBottomSet lambda :=
    rlc_strictBottomSet_mono_of_disjoint_path gamma lambda hdisjGamma
  have hbottomDelta : rlc_strictBottomSet delta ⊆
      rlc_strictBottomSet lambda :=
    rlc_strictBottomSet_mono_of_disjoint_path delta lambda hdisjDelta
  intro z hz
  rw [Finset.mem_inter]
  rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hz
  constructor
  · rw [rlc_leftExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzBottom
    exact hz.2 (by
      simpa using hbottomGamma (by simpa using hzBottom))
  · rw [rlc_leftExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzBottom
    exact hz.2 (by
      simpa using hbottomDelta (by simpa using hzBottom))


theorem rlc_envelopeProperties_of_rightSafeTraceReachability {n : ℤ}
    (hsafe : RlcRightSafeTraceReachability n) :
    RlcRightEnvelopeProperty n ∧ RlcLeftEnvelopeProperty n := by
  have hright : RlcRightFrontierPathProperty n :=
    rlc_rightFrontierPathProperty_of_safeTraceReachability hsafe
  have hleft : RlcLeftFrontierPathProperty n :=
    rlc_leftFrontierPathProperty_of_right hright
  exact ⟨rlc_rightEnvelopeProperty_of_frontierPath hright,
    rlc_leftEnvelopeProperty_of_frontierPath hleft⟩

theorem rlc_pathOpen_of_edges_subset_union {a b c d : ℤ}
    (lambda gamma delta : RlcCrossingPath a b c d)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hedges : rlc_pathEdges lambda ⊆
      rlc_pathEdges gamma ∪ rlc_pathEdges delta)
    (hgamma : omega ∈ rlc_pathOpen gamma)
    (hdelta : omega ∈ rlc_pathOpen delta) :
    omega ∈ rlc_pathOpen lambda := by
  intro e he
  rcases Finset.mem_union.mp (hedges he) with he | he
  · exact hgamma e he
  · exact hdelta e he

theorem rlc_rightLowestCandidate_pairwiseDisjoint {n : ℤ}
    (henv : RlcRightEnvelopeProperty n) :
    Pairwise (Disjoint on fun gamma : RlcRightDiagonalPath n =>
      rlc_rightLowestCandidate gamma) := by
  intro gamma delta hne
  change Disjoint (rlc_rightLowestCandidate gamma)
    (rlc_rightLowestCandidate delta)
  rw [Set.disjoint_left]
  intro omega hgamma hdelta
  obtain ⟨lambda, hedges, hregion⟩ := henv gamma delta
  have hlambda : omega ∈ rlc_pathOpen lambda.1 :=
    rlc_pathOpen_of_edges_subset_union lambda.1 gamma.1 delta.1 hedges
      hgamma.1 hdelta.1
  have hLG : rlc_rightExploredVertices lambda ⊆
      rlc_rightExploredVertices gamma := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).1
  have hLD : rlc_rightExploredVertices lambda ⊆
      rlc_rightExploredVertices delta := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).2
  by_cases hEqLG : rlc_rightExploredVertices lambda =
      rlc_rightExploredVertices gamma
  · have hGD : rlc_rightExploredVertices gamma ⊆
        rlc_rightExploredVertices delta := by
      intro z hz
      exact hLD (hEqLG.symm ▸ hz)
    by_cases hEqGD : rlc_rightExploredVertices gamma =
        rlc_rightExploredVertices delta
    · have hindex : rlc_rightPathIndex gamma ≠
          rlc_rightPathIndex delta := by
        intro hidx
        apply hne
        apply (Fintype.equivFin (RlcRightDiagonalPath n)).injective
        apply Fin.ext
        exact hidx
      rcases lt_or_gt_of_ne hindex with hlt | hgt
      · exact (rlc_rightLowestCandidate_not_open_of_below hdelta
          (Or.inr ⟨hEqGD, hlt⟩)) hgamma.1
      · exact (rlc_rightLowestCandidate_not_open_of_below hgamma
          (Or.inr ⟨hEqGD.symm, hgt⟩)) hdelta.1
    · have hstrict : rlc_rightExploredVertices gamma ⊂
          rlc_rightExploredVertices delta :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hGD, hEqGD⟩
      exact (rlc_rightLowestCandidate_not_open_of_below hdelta
        (Or.inl hstrict)) hgamma.1
  · have hstrict : rlc_rightExploredVertices lambda ⊂
        rlc_rightExploredVertices gamma :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hLG, hEqLG⟩
    exact (rlc_rightLowestCandidate_not_open_of_below hgamma
      (Or.inl hstrict)) hlambda

theorem rlc_leftHighestCandidate_pairwiseDisjoint {n : ℤ}
    (henv : RlcLeftEnvelopeProperty n) :
    Pairwise (Disjoint on fun gamma : RlcLeftDiagonalPath n =>
      rlc_leftHighestCandidate gamma) := by
  intro gamma delta hne
  change Disjoint (rlc_leftHighestCandidate gamma)
    (rlc_leftHighestCandidate delta)
  rw [Set.disjoint_left]
  intro omega hgamma hdelta
  obtain ⟨lambda, hedges, hregion⟩ := henv gamma delta
  have hlambda : omega ∈ rlc_pathOpen lambda.1 :=
    rlc_pathOpen_of_edges_subset_union lambda.1 gamma.1 delta.1 hedges
      hgamma.1 hdelta.1
  have hLG : rlc_leftExploredVertices lambda ⊆
      rlc_leftExploredVertices gamma := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).1
  have hLD : rlc_leftExploredVertices lambda ⊆
      rlc_leftExploredVertices delta := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).2
  by_cases hEqLG : rlc_leftExploredVertices lambda =
      rlc_leftExploredVertices gamma
  · have hGD : rlc_leftExploredVertices gamma ⊆
        rlc_leftExploredVertices delta := by
      intro z hz
      exact hLD (hEqLG.symm ▸ hz)
    by_cases hEqGD : rlc_leftExploredVertices gamma =
        rlc_leftExploredVertices delta
    · have hindex : rlc_leftPathIndex gamma ≠
          rlc_leftPathIndex delta := by
        intro hidx
        apply hne
        apply (Fintype.equivFin (RlcLeftDiagonalPath n)).injective
        apply Fin.ext
        exact hidx
      rcases lt_or_gt_of_ne hindex with hlt | hgt
      · exact (rlc_leftHighestCandidate_not_open_of_above hdelta
          (Or.inr ⟨hEqGD, hlt⟩)) hgamma.1
      · exact (rlc_leftHighestCandidate_not_open_of_above hgamma
          (Or.inr ⟨hEqGD.symm, hgt⟩)) hdelta.1
    · have hstrict : rlc_leftExploredVertices gamma ⊂
          rlc_leftExploredVertices delta :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hGD, hEqGD⟩
      exact (rlc_leftHighestCandidate_not_open_of_above hdelta
        (Or.inl hstrict)) hgamma.1
  · have hstrict : rlc_leftExploredVertices lambda ⊂
        rlc_leftExploredVertices gamma :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hLG, hEqLG⟩
    exact (rlc_leftHighestCandidate_not_open_of_above hgamma
      (Or.inl hstrict)) hlambda

theorem rlc_extremalPairCandidate_pairwiseDisjoint {n : ℤ}
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise (Disjoint on fun pair : RlcDiagonalPathPair n =>
      rlc_extremalPairCandidate pair) := by
  intro pair pair' hne
  by_cases hrightEq : pair.1 = pair'.1
  · have hleftNe : pair.2 ≠ pair'.2 := fun h =>
      hne (Prod.ext hrightEq h)
    exact (rlc_leftHighestCandidate_pairwiseDisjoint hleft hleftNe).mono
      inter_subset_right inter_subset_right
  · exact (rlc_rightLowestCandidate_pairwiseDisjoint hright hrightEq).mono
      inter_subset_left inter_subset_left

end Universality
end StatMech
