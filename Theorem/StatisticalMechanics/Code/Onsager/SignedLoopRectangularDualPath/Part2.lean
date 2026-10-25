/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

@[simp] theorem ons_rectDualPathDefectWeight_of_mem
    {M N : Nat} (path : ons_RectDualPath M N) (x : Real)
    {edge : Sym2 (ons_RectDualVertex M N)}
    (hedge : edge ∈ ons_rectDualPathDefect path) :
    ons_rectDualPathDefectWeight path x edge = (x : Complex)⁻¹ := by
  simp [ons_rectDualPathDefectWeight, hedge]

@[simp] theorem ons_rectDualPathDefectWeight_of_not_mem
    {M N : Nat} (path : ons_RectDualPath M N) (x : Real)
    {edge : Sym2 (ons_RectDualVertex M N)}
    (hedge : edge ∉ ons_rectDualPathDefect path) :
    ons_rectDualPathDefectWeight path x edge = (x : Complex) := by
  simp [ons_rectDualPathDefectWeight, hedge]


end
end StatMech.Onsager
