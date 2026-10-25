/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.HasPrimitives
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive
open Complex Filter Metric Set Topology


namespace StatMech.FrontierA

open StatMech.FK


noncomputable def leeYangCayleyPulledDerivative
    (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  g (leeYangRightCayleyInv w) * (2 / (1 - w) ^ 2)

end StatMech.FrontierA
