/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part4
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.OpenMapping
open Filter Set Topology


namespace StatMech.Universality

noncomputable def isingFermionicEntireSquarePrimitive
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.wedgeIntegral 0 z (fun w ↦ f w ^ 2)

end StatMech.Universality
