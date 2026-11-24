module
public import Theorem.StatisticalMechanics.Code.FrontierB.BoundarySourceParity.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceBoxCurrent.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit.Part4
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
open Filter MeasureTheory
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceCurrentLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Lattice


noncomputable def growingPlusPairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let hNk : N ≤ k + N := Nat.le_add_left N k
  plusPairSourceBoxCurrentMeasure d (k + N) beta hbeta
    (pairSourceBoxSite x (box_mono d hNk hx))
    (pairSourceBoxSite y (box_mono d hNk hy))
    (pairSourceBoxSite_ne _ _ hxy)


end StatMech.FrontierB
