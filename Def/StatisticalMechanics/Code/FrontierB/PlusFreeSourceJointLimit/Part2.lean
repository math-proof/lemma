/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceCurrentLimit
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Structure.StatisticalMechanics.Code.FrontierB.PlusFreeSourceJointLimit
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


noncomputable def plusFreeSourceJointLimitData
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    PlusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy := by
  exact Classical.choice
    (show Nonempty
      (PlusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy) from by
      obtain ⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩ :=
        plusFreeSourceCurrentMeasure_joint_subsequence
          d N beta hbeta x y hx hy hxy
      exact ⟨⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩⟩)


noncomputable def infiniteFreePairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (plusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy).freeSourceLimit


noncomputable def infinitePlusPairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (plusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy).plusSourceLimit


noncomputable def plusFreeSourceCurrentSubsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) : ℕ → ℕ :=
  (plusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy).subsequence

end StatMech.FrontierB
