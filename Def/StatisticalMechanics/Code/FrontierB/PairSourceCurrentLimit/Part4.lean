/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxCurrentParity
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Structure.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


noncomputable def pairSourceCurrentLimitData
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    PairSourceCurrentLimitData d N beta hbeta x y hx hy hxy := by
  exact Classical.choice
    (show Nonempty (PairSourceCurrentLimitData d N beta hbeta x y hx hy hxy) from by
      obtain ⟨nu, phi, hphi, hweak⟩ :=
        growingPairSourceCurrentMeasure_subsequence d N beta hbeta x y hx hy hxy
      exact ⟨⟨nu, phi, hphi, hweak⟩⟩)


noncomputable def infinitePairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).limit

noncomputable def pairSourceCurrentBoxSubsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) : ℕ → ℕ :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).subsequence

end StatMech.FrontierB
