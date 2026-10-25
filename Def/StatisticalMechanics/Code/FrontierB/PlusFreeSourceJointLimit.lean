/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceCurrentLimit
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


noncomputable def growingFreePairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let n := (k + N) + 1
  let hNn : N ≤ n := le_trans (Nat.le_add_left N k) (Nat.le_succ _)
  pairSourceBoxCurrentMeasure d n beta hbeta
    (pairSourceBoxSite x (box_mono d hNn hx))
    (pairSourceBoxSite y (box_mono d hNn hy))
    (pairSourceBoxSite_ne _ _ hxy)


end StatMech.FrontierB
