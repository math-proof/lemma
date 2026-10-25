/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders.Part2
import Structure.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
open Filter MeasureTheory


namespace StatMech.FrontierB

open Lattice

noncomputable def freePlusCurrentLimitData
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    FreePlusCurrentLimitData d beta hbeta := by
  exact Classical.choice (show Nonempty (FreePlusCurrentLimitData d beta hbeta) from by
    obtain ⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩ :=
      freePlusBoxCurrentMeasure_joint_subsequence d beta hbeta
    exact ⟨⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩⟩)

noncomputable def infiniteFreeCurrentMeasure
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (freePlusCurrentLimitData d beta hbeta).freeLimit

noncomputable def infinitePlusCurrentMeasure
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (freePlusCurrentLimitData d beta hbeta).plusLimit

noncomputable def infiniteCurrentBoxSubsequence
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) : ℕ → ℕ :=
  (freePlusCurrentLimitData d beta hbeta).subsequence

end StatMech.FrontierB
