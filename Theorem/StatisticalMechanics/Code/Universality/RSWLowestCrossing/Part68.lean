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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part67
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_exists_min_rightCommonSupport {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∀ q : ↑(rlc_rightCommonSupport gamma delta),
        rlc_rightCommonRank gamma delta z ≤
          rlc_rightCommonRank gamma delta q := by
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
    (rlc_rightCommonRank gamma delta) huniv
  exact ⟨z, fun q => hmin q (by simp)⟩


theorem rlc_min_rightCommon_prefixes_inter_only {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta))
    (hzGamma : z.1 ∈ gamma.1.2.2.1.support)
    (hzDelta : z.1 ∈ delta.1.2.2.1.support)
    (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta),
      rlc_rightCommonRank gamma delta z ≤
        rlc_rightCommonRank gamma delta q)
    {q : rect 0 (2 * n) (-n) n}
    (hqGamma : q ∈ (gamma.1.2.2.1.takeUntil z.1 hzGamma).support)
    (hqDelta : q ∈ (delta.1.2.2.1.takeUntil z.1 hzDelta).support) :
    q = z.1 := by
  classical
  by_contra hqz
  have hqGammaFull : q ∈ gamma.1.2.2.1.support :=
    gamma.1.2.2.1.support_takeUntil_subset_support hzGamma hqGamma
  have hqDeltaFull : q ∈ delta.1.2.2.1.support :=
    delta.1.2.2.1.support_takeUntil_subset_support hzDelta hqDelta
  have hqCommon : q ∈ rlc_rightCommonSupport gamma delta := by
    simp [rlc_rightCommonSupport, hqGammaFull, hqDeltaFull]
  let qs : ↑(rlc_rightCommonSupport gamma delta) := ⟨q, hqCommon⟩
  have hgammaLt :
      (gamma.1.2.2.1.takeUntil q hqGammaFull).length <
        (gamma.1.2.2.1.takeUntil z.1 hzGamma).length := by
    have hlen := (gamma.1.2.2.1.takeUntil z.1 hzGamma).length_takeUntil_lt
      hqGamma hqz
    rwa [gamma.1.2.2.1.takeUntil_takeUntil hzGamma hqGamma] at hlen
  have hdeltaLt :
      (delta.1.2.2.1.takeUntil q hqDeltaFull).length <
        (delta.1.2.2.1.takeUntil z.1 hzDelta).length := by
    have hlen := (delta.1.2.2.1.takeUntil z.1 hzDelta).length_takeUntil_lt
      hqDelta hqz
    rwa [delta.1.2.2.1.takeUntil_takeUntil hzDelta hqDelta] at hlen
  have hrankLt : rlc_rightCommonRank gamma delta qs <
      rlc_rightCommonRank gamma delta z := by
    change (gamma.1.2.2.1.takeUntil q hqGammaFull).length +
        (delta.1.2.2.1.takeUntil q hqDeltaFull).length <
      (gamma.1.2.2.1.takeUntil z.1 hzGamma).length +
        (delta.1.2.2.1.takeUntil z.1 hzDelta).length
    omega
  exact (not_lt_of_ge (hmin qs)) hrankLt


end Universality
end StatMech
