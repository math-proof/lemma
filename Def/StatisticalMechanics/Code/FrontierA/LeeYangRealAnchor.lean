module
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangNormalFamilyReduction
public import Theorem.StatisticalMechanics.Code.Ising.PressureConvex
public import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
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


noncomputable def isingBoxPressureLimit
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) : ℝ :=
  Classical.choose (isingBoxPressure_tendsto d hd beta h)

end StatMech.FrontierA
