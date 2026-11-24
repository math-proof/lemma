module
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangNormalFamilyReduction
public import Theorem.StatisticalMechanics.Code.Ising.PressureConvex
public import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part3
open Filter Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


def leeYangRightRealAnchor
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) : Set ℂ :=
  {z | z.im = 0 ∧ 0 < z.re ∧
    z.re ∈ leeYangPressureRegularRealSet d hd beta}

end StatMech.FrontierA
