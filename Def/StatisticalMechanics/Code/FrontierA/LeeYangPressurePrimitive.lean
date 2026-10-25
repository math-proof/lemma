/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.HasPrimitives
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part4
open Complex Filter Metric Set Topology


namespace StatMech.FrontierA

open StatMech.FK


noncomputable def leeYangRightCayley (z : ℂ) : ℂ := (z - 1) / (z + 1)


noncomputable def leeYangRightCayleyInv (w : ℂ) : ℂ := (1 + w) / (1 - w)

end StatMech.FrontierA
