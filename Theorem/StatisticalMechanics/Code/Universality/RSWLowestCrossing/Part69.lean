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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part68
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_exists_min_gamma_reverse_rightCommonSupport {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∀ q : ↑(rlc_rightCommonSupport gamma delta),
        rlc_rightCommonGammaReverseRank gamma delta z ≤
          rlc_rightCommonGammaReverseRank gamma delta q := by
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
    (rlc_rightCommonGammaReverseRank gamma delta) huniv
  exact ⟨z, fun q => hmin q (by simp)⟩


theorem rlc_min_gamma_reverse_rightCommon_prefix_inter_only {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta))
    (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
    (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta),
      rlc_rightCommonGammaReverseRank gamma delta z ≤
        rlc_rightCommonGammaReverseRank gamma delta q)
    {q : rect 0 (2 * n) (-n) n}
    (hqGamma : q ∈
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).support)
    (hqDelta : q ∈ delta.1.2.2.1.support) :
    q = z.1 := by
  classical
  by_contra hqz
  have hqGammaRev : q ∈ gamma.1.2.2.1.reverse.support :=
    gamma.1.2.2.1.reverse.support_takeUntil_subset_support
      hzGamma hqGamma
  have hqGammaOrig : q ∈ gamma.1.2.2.1.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hqGammaRev
  have hqCommon : q ∈ rlc_rightCommonSupport gamma delta := by
    simp [rlc_rightCommonSupport, hqGammaOrig, hqDelta]
  let qs : ↑(rlc_rightCommonSupport gamma delta) := ⟨q, hqCommon⟩
  have hrankLt : rlc_rightCommonGammaReverseRank gamma delta qs <
      rlc_rightCommonGammaReverseRank gamma delta z := by
    change (gamma.1.2.2.1.reverse.takeUntil q hqGammaRev).length <
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length
    have hlen :=
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length_takeUntil_lt
        hqGamma hqz
    rwa [gamma.1.2.2.1.reverse.takeUntil_takeUntil hzGamma hqGamma] at hlen
  exact (not_lt_of_ge (hmin qs)) hrankLt


theorem rlc_last_gamma_terminal_suffix_top_of_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : ↑(rlc_rightCommonSupport gamma delta))
      (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support),
      let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
      ¬ pg.Nil ∧
        (∀ q ∈ pg.dropLast.support,
          (q : Site 2) ∉ rlc_pathVertices delta.1) ∧
        (∀ q ∈ pg.dropLast.support,
          (q : Site 2) ∈ rlc_strictTopSet delta) := by
  classical
  obtain ⟨z, hmin⟩ :=
    rlc_exists_min_gamma_reverse_rightCommonSupport gamma delta hinter
  have hzBoth := Finset.mem_inter.mp z.2
  have hzGammaOrig : z.1 ∈ gamma.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.1
  have hzDeltaOrig : z.1 ∈ delta.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.2
  have hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzGammaOrig
  have hzPathGamma : (z.1 : Site 2) ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzGammaOrig, rfl⟩
  have hzPathDelta : (z.1 : Site 2) ∈ rlc_pathVertices delta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzDeltaOrig, rfl⟩
  have hzSafe := rlc_commonRightPathVertex_not_upperUnion
    gamma delta hzPathGamma hzPathDelta
  have hzNeEnd :
      (⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ :
        rect 0 (2 * n) (-n) n) ≠ z.1 := by
    intro h
    apply hzSafe
    have hval := congrArg Subtype.val h
    simpa using hval ▸ hgammaEnd
  have hgammaEndPath : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hgammaTopDelta : (gamma.1.2.1 : Site 2) ∈
      rlc_strictTopSet delta := by
    rcases hgammaEnd with htopGamma | htopDelta
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) htopGamma hgammaEndPath)
    · exact htopDelta
  let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
  have hpg : ¬ pg.Nil := SimpleGraph.Walk.not_nil_of_ne hzNeEnd
  have hpgPath : pg.IsPath :=
    gamma.1.2.2.2.reverse.takeUntil hzGamma
  have hzNotDrop : z.1 ∉ pg.dropLast.support := by
    have hn := hpgPath.support_nodup
    rw [← pg.support_dropLast_concat hpg] at hn
    have hd : List.Disjoint pg.dropLast.support [z.1] :=
      List.disjoint_of_nodup_append hn
    intro hz
    exact (List.disjoint_left.mp hd) hz (by simp)
  have hAvoid : ∀ q ∈ pg.dropLast.support,
      (q : Site 2) ∉ rlc_pathVertices delta.1 := by
    intro q hq hqDeltaPath
    have hqPg : q ∈ pg.support := by
      rw [← pg.support_dropLast_concat hpg]
      exact List.mem_append_left _ hq
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hqDeltaPath
    obtain ⟨u, huDelta, huq⟩ := hqDeltaPath
    have hueq : u = q := by
      apply Subtype.ext
      exact huq
    subst u
    have hqz := rlc_min_gamma_reverse_rightCommon_prefix_inter_only
      gamma delta z hzGamma hmin hqPg huDelta
    exact hzNotDrop (hqz ▸ hq)
  have hTop : ∀ q ∈ pg.dropLast.support,
      (q : Site 2) ∈ rlc_strictTopSet delta := by
    intro q hq
    exact (rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids
      delta pg.dropLast hAvoid hq).mpr hgammaTopDelta
  exact ⟨z, hzGamma, hpg, hAvoid, hTop⟩


theorem rlc_last_delta_terminal_suffix_top_of_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : ↑(rlc_rightCommonSupport delta gamma))
      (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support),
      let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta
      ¬ pd.Nil ∧
        (∀ q ∈ pd.dropLast.support,
          (q : Site 2) ∉ rlc_pathVertices gamma.1) ∧
        (∀ q ∈ pd.dropLast.support,
          (q : Site 2) ∈ rlc_strictTopSet gamma) := by
  apply rlc_last_gamma_terminal_suffix_top_of_unsafe_end delta gamma
  · exact fun h => hinter h.symm
  · simpa [rlc_rightUpperUnionSet, Set.union_comm] using hdeltaEnd


theorem rlc_last_common_reaches_safe_gamma_endpoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      (rlc_rightSafeTraceGraph gamma delta).Reachable z.1
        ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ := by
  classical
  obtain ⟨z, hmin⟩ :=
    rlc_exists_min_gamma_reverse_rightCommonSupport gamma delta hinter
  have hzBoth := Finset.mem_inter.mp z.2
  have hzGammaOrig : z.1 ∈ gamma.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.1
  have hzDeltaOrig : z.1 ∈ delta.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.2
  have hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzGammaOrig
  let y : rect 0 (2 * n) (-n) n :=
    ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩
  by_cases hyz : y = z.1
  · exact ⟨z, hyz ▸ SimpleGraph.Reachable.refl y⟩
  let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
  have hpg : ¬ pg.Nil := SimpleGraph.Walk.not_nil_of_ne hyz
  have hpgPath : pg.IsPath := gamma.1.2.2.2.reverse.takeUntil hzGamma
  have hzNotDrop : z.1 ∉ pg.dropLast.support := by
    have hn := hpgPath.support_nodup
    rw [← pg.support_dropLast_concat hpg] at hn
    have hd : List.Disjoint pg.dropLast.support [z.1] :=
      List.disjoint_of_nodup_append hn
    intro hz
    exact (List.disjoint_left.mp hd) hz (by simp)
  have hAvoid : ∀ q ∈ pg.dropLast.support,
      (q : Site 2) ∉ rlc_pathVertices delta.1 := by
    intro q hq hqDeltaPath
    have hqPg : q ∈ pg.support := by
      rw [← pg.support_dropLast_concat hpg]
      exact List.mem_append_left _ hq
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hqDeltaPath
    obtain ⟨u, huDelta, huq⟩ := hqDeltaPath
    have hueq : u = q := by
      apply Subtype.ext
      exact huq
    subst u
    have hqz := rlc_min_gamma_reverse_rightCommon_prefix_inter_only
      gamma delta z hzGamma hmin hqPg huDelta
    exact hzNotDrop (hqz ▸ hq)
  have hEndNotTopDelta : (gamma.1.2.1 : Site 2) ∉
      rlc_strictTopSet delta := fun h => hgammaEnd (Or.inr h)
  have hSupportSafe : ∀ q ∈ pg.support,
      (q : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
    intro q hq
    have hqGammaRev : q ∈ gamma.1.2.2.1.reverse.support :=
      gamma.1.2.2.1.reverse.support_takeUntil_subset_support hzGamma hq
    have hqGammaOrig : q ∈ gamma.1.2.2.1.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hqGammaRev
    have hqPathGamma : (q : Site 2) ∈ rlc_pathVertices gamma.1 := by
      simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
      exact ⟨q, hqGammaOrig, rfl⟩
    intro hupper
    rcases hupper with htopGamma | htopDelta
    · exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path gamma))
        htopGamma hqPathGamma
    · by_cases hqz : q = z.1
      · subst q
        have hzPathDelta : (z.1 : Site 2) ∈
            rlc_pathVertices delta.1 := by
          simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
          exact ⟨z.1, hzDeltaOrig, rfl⟩
        exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path delta))
          htopDelta hzPathDelta
      · have hqDrop : q ∈ pg.dropLast.support := by
          have hq' := hq
          rw [← pg.support_dropLast_concat hpg] at hq'
          simp only [List.mem_append, List.mem_singleton] at hq'
          exact hq'.resolve_right hqz
        have hiff := rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids
          delta pg.dropLast hAvoid hqDrop
        exact hEndNotTopDelta (hiff.mp htopDelta)
  have pSafe : (rlc_rightSafeTraceGraph gamma delta).Walk y z.1 := by
    apply pg.transfer (rlc_rightSafeTraceGraph gamma delta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have heRev : s(u, v) ∈ gamma.1.2.2.1.reverse.edges :=
          gamma.1.2.2.1.reverse.edges_takeUntil_subset hzGamma he
        have heOrig : s(u, v) ∈ gamma.1.2.2.1.edges := by
          simpa [SimpleGraph.Walk.edges_reverse] using heRev
        have hePath : s((u : Site 2), (v : Site 2)) ∈
            rlc_pathEdges gamma.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(u, v), heOrig, rfl⟩
        exact rlc_rightSafeTraceGraph_adj_of_pathEdge gamma delta
          (Finset.mem_union_left _ hePath)
          (hSupportSafe u (pg.fst_mem_support_of_mem_edges he))
          (hSupportSafe v (pg.snd_mem_support_of_mem_edges he))
  exact ⟨z, ⟨pSafe.reverse⟩⟩


theorem rlc_last_common_reaches_safe_delta_endpoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta) :
    ∃ z : ↑(rlc_rightCommonSupport delta gamma),
      (rlc_rightSafeTraceGraph gamma delta).Reachable z.1
        ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
  obtain ⟨z, hz⟩ := rlc_last_common_reaches_safe_gamma_endpoint
    delta gamma (fun h => hinter h.symm)
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hdeltaEnd)
  refine ⟨z, ?_⟩
  simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
    Finset.union_comm, Set.union_comm] using hz


end Universality
end StatMech
