/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionReduction
open Set Filter Topology


namespace StatMech.Ising

def HasOrderedMagnetizationRegime (M : ℝ → ℝ) (betaC : ℝ) : Prop :=
  0 < betaC ∧
    (∀ beta, 0 ≤ beta → beta ≤ betaC → M beta = 0) ∧
    (∀ beta, betaC < beta → 0 < M beta)


end StatMech.Ising
