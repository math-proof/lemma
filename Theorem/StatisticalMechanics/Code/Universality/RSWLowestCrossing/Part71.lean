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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part70
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightSafeTraceReachability_of_canonicalAnchor {n : ℤ}
    (hn : 0 < n) (hanchor : RlcRightCanonicalAnchorReachability n) :
    RlcRightSafeTraceReachability n := by
  intro gamma delta
  let x := rlc_rightLeftTraceMinSide gamma delta
  obtain ⟨y, hyHalf, hySafe, hxy⟩ := hanchor gamma delta
  refine ⟨x, y, ?_, hyHalf, ?_, hySafe, hxy⟩
  · simpa [x] using rlc_rightLeftTraceMinVertex_lowerHalf gamma delta
  · simpa [x] using
      rlc_rightLeftTraceMinVertex_not_upperUnion hn gamma delta


theorem rlc_exists_min_reverse_rightCommonSupport {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∀ q : ↑(rlc_rightCommonSupport gamma delta),
        rlc_rightCommonReverseRank gamma delta z ≤
          rlc_rightCommonReverseRank gamma delta q := by
  classical
  have hne := rlc_rightCommonSupport_nonempty_of_not_disjoint
    gamma delta hinter
  letI : Nonempty ↑(rlc_rightCommonSupport gamma delta) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have huniv : (Finset.univ :
      Finset ↑(rlc_rightCommonSupport gamma delta)).Nonempty :=
    ⟨⟨hne.choose, hne.choose_spec⟩, Finset.mem_univ _⟩
  obtain ⟨z, _hz, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset ↑(rlc_rightCommonSupport gamma delta))
    (rlc_rightCommonReverseRank gamma delta) huniv
  exact ⟨z, fun q => hmin q (by simp)⟩


theorem rlc_min_reverse_rightCommon_prefixes_inter_only {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta))
    (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
    (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support)
    (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta),
      rlc_rightCommonReverseRank gamma delta z ≤
        rlc_rightCommonReverseRank gamma delta q)
    {q : rect 0 (2 * n) (-n) n}
    (hqGamma : q ∈
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).support)
    (hqDelta : q ∈
      (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).support) :
    q = z.1 := by
  classical
  by_contra hqz
  have hqGammaFull : q ∈ gamma.1.2.2.1.reverse.support :=
    gamma.1.2.2.1.reverse.support_takeUntil_subset_support hzGamma hqGamma
  have hqDeltaFull : q ∈ delta.1.2.2.1.reverse.support :=
    delta.1.2.2.1.reverse.support_takeUntil_subset_support hzDelta hqDelta
  have hqCommon : q ∈ rlc_rightCommonSupport gamma delta := by
    have hqGammaOrig : q ∈ gamma.1.2.2.1.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hqGammaFull
    have hqDeltaOrig : q ∈ delta.1.2.2.1.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hqDeltaFull
    simp [rlc_rightCommonSupport, hqGammaOrig, hqDeltaOrig]
  let qs : ↑(rlc_rightCommonSupport gamma delta) := ⟨q, hqCommon⟩
  have hgammaLt :
      (gamma.1.2.2.1.reverse.takeUntil q hqGammaFull).length <
        (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length := by
    have hlen :=
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length_takeUntil_lt
        hqGamma hqz
    rwa [gamma.1.2.2.1.reverse.takeUntil_takeUntil hzGamma hqGamma] at hlen
  have hdeltaLt :
      (delta.1.2.2.1.reverse.takeUntil q hqDeltaFull).length <
        (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).length := by
    have hlen :=
      (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).length_takeUntil_lt
        hqDelta hqz
    rwa [delta.1.2.2.1.reverse.takeUntil_takeUntil hzDelta hqDelta] at hlen
  have hrankLt : rlc_rightCommonReverseRank gamma delta qs <
      rlc_rightCommonReverseRank gamma delta z := by
    change (gamma.1.2.2.1.reverse.takeUntil q hqGammaFull).length +
        (delta.1.2.2.1.reverse.takeUntil q hqDeltaFull).length <
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length +
        (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).length
    omega
  exact (not_lt_of_ge (hmin qs)) hrankLt


theorem rlc_terminal_lens_of_unsafe_ends {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta)
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∃ (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
        (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support),
      (z.1 : Site 2) ≠ (gamma.1.2.1 : Site 2) ∧
      (z.1 : Site 2) ≠ (delta.1.2.1 : Site 2) ∧
      ∀ q : rect 0 (2 * n) (-n) n,
        q ∈ (gamma.1.2.2.1.reverse.takeUntil z.1
          hzGamma).support →
        q ∈ (delta.1.2.2.1.reverse.takeUntil z.1
          hzDelta).support →
        q = z.1 := by
  classical
  obtain ⟨z, hmin⟩ :=
    rlc_exists_min_reverse_rightCommonSupport gamma delta hinter
  have hzBoth := Finset.mem_inter.mp z.2
  have hzGamma : z.1 ∈ gamma.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.1
  have hzDelta : z.1 ∈ delta.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.2
  have hzGammaRev : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzGamma
  have hzDeltaRev : z.1 ∈ delta.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzDelta
  have hzPathGamma : (z.1 : Site 2) ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzGamma, rfl⟩
  have hzPathDelta : (z.1 : Site 2) ∈ rlc_pathVertices delta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzDelta, rfl⟩
  have hzSafe := rlc_commonRightPathVertex_not_upperUnion
    gamma delta hzPathGamma hzPathDelta
  have hzNeGamma : (z.1 : Site 2) ≠ (gamma.1.2.1 : Site 2) := by
    intro h
    apply hzSafe
    rwa [h]
  have hzNeDelta : (z.1 : Site 2) ≠ (delta.1.2.1 : Site 2) := by
    intro h
    apply hzSafe
    rwa [h]
  refine ⟨z, hzGammaRev, hzDeltaRev, hzNeGamma, hzNeDelta, ?_⟩
  intro q hqGamma hqDelta
  exact rlc_min_reverse_rightCommon_prefixes_inter_only gamma delta z
    hzGammaRev hzDeltaRev hmin hqGamma hqDelta


theorem rlc_lens_penultimate_ne {V : Type*} {G : SimpleGraph V}
    {a b z : V} (p : G.Walk a z) (q : G.Walk b z)
    (ha : a ≠ z) (hb : b ≠ z)
    (hinter : ∀ u : V, u ∈ p.support → u ∈ q.support → u = z) :
    p.penultimate ≠ q.penultimate := by
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne ha
  have hq : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne hb
  intro heq
  have hpMem : p.penultimate ∈ p.support := p.getVert_mem_support _
  have hqMem : p.penultimate ∈ q.support := by
    rw [heq]
    exact q.getVert_mem_support _
  have hpz : p.penultimate = z := hinter p.penultimate hpMem hqMem
  exact (p.adj_penultimate hp).ne hpz


theorem rlc_terminal_lens_distinct_branches_of_unsafe_ends {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta)
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : ↑(rlc_rightCommonSupport gamma delta))
      (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
      (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support),
      let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
      let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta
      ¬ pg.Nil ∧ ¬ pd.Nil ∧
        ((hypercubicLattice 2).induce
          (rect 0 (2 * n) (-n) n)).Adj pg.penultimate z.1 ∧
        ((hypercubicLattice 2).induce
          (rect 0 (2 * n) (-n) n)).Adj pd.penultimate z.1 ∧
        pg.penultimate ≠ pd.penultimate := by
  obtain ⟨z, hzGamma, hzDelta, hzNeGamma, hzNeDelta, hOnly⟩ :=
    rlc_terminal_lens_of_unsafe_ends gamma delta hinter
      hgammaEnd hdeltaEnd
  let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
  let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta
  have hpgStart :
      (⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ :
        rect 0 (2 * n) (-n) n) ≠ z.1 := by
    intro h
    apply hzNeGamma
    exact congrArg Subtype.val h.symm
  have hpdStart :
      (⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ :
        rect 0 (2 * n) (-n) n) ≠ z.1 := by
    intro h
    apply hzNeDelta
    exact congrArg Subtype.val h.symm
  have hpg : ¬ pg.Nil := SimpleGraph.Walk.not_nil_of_ne hpgStart
  have hpd : ¬ pd.Nil := SimpleGraph.Walk.not_nil_of_ne hpdStart
  have hbranches : pg.penultimate ≠ pd.penultimate :=
    rlc_lens_penultimate_ne pg pd hpgStart hpdStart hOnly
  exact ⟨z, hzGamma, hzDelta, hpg, hpd,
    pg.adj_penultimate hpg, pd.adj_penultimate hpd, hbranches⟩


theorem rlc_rightSafeTraceReachability_of_intersecting {n : ℤ} (hn : 0 < n)
    (hinter : RlcRightIntersectingSafeTraceReachability n) :
    RlcRightSafeTraceReachability n := by
  intro gamma delta
  by_cases hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)
  · exact rlc_rightSafeTraceReachable_of_disjoint hn gamma delta hdisj
  · exact hinter gamma delta hdisj

theorem rlc_rightSafeTraceGraph_walk_support_safe {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {x y : rect 0 (2 * n) (-n) n}
    (w : (rlc_rightSafeTraceGraph gamma delta).Walk x y)
    (hx : (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    {z : rect 0 (2 * n) (-n) n} (hz : z ∈ w.support) :
    (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  induction w with
  | nil =>
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hx
  | @cons a b c hab w ih =>
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hab.2.2.1
      · exact ih hab.2.2.2 hz


end Universality
end StatMech
