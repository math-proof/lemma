/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceCurrentLimit
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusFreeSourceJointLimit
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


structure PlusFreeSourceJointLimitData
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) where
  freeSourceLimit : ProbabilityMeasure
    (InfiniteCurrentConfig (Sym2 (Site d)))
  plusSourceLimit : ProbabilityMeasure
    (InfiniteCurrentConfig (Sym2 (Site d)))
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  freeSource_tendsto : WeakCurrentConverges
    ((growingFreePairSourceCurrentMeasure
      d N beta hbeta x y hx hy hxy) ∘ subsequence) freeSourceLimit
  plusSource_tendsto : WeakCurrentConverges
    ((growingPlusPairSourceCurrentMeasure
      d N beta hbeta x y hx hy hxy) ∘ subsequence) plusSourceLimit

end StatMech.FrontierB
