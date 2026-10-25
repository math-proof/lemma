/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
open Set Filter Topology


namespace StatMech.Ising

def HasWeakSurfaceTensionLowerBound
    (J : ℝ) (M tau : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b →
    2 * J * (M a) ^ 2 * (b - a) ≤ tau b - tau a


end StatMech.Ising
