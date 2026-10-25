/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangNormalFamilyReduction
import Theorem.StatisticalMechanics.Code.Ising.PressureConvex
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


noncomputable def isingBoxPressureFieldDerivative
    (d n : ℕ) (beta h : ℝ) : ℝ :=
  beta * isingExpectation (boxGraph d n) beta h
      (fun s => ∑ v, spin s v) /
    (Fintype.card (boxVerts d n) : ℝ)

end StatMech.FrontierA
