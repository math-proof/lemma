module
public import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxCurrentParity
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit
open Filter MeasureTheory
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Ising Lattice


noncomputable def pairSourceBaseConstant
    (d N : ℕ) (beta : ℝ) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) : ℝ :=
  boxPairCorrelationConstant d N beta
    (pairSourceBoxSite x hx) (pairSourceBoxSite y hy)

end StatMech.FrontierB
