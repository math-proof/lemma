/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FiniteHolomorphicInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
open Finset


noncomputable section

noncomputable def finiteLagrangeBasis
    {α : Type*} [Fintype α] [DecidableEq α]
    (position : α → Complex) (a : α) (z : Complex) : Complex :=
  ∏ b ∈ Finset.univ.erase a, (z - position b) / (position a - position b)


noncomputable def finiteLagrangeInterpolant
    {α : Type*} [Fintype α] [DecidableEq α]
    (position value : α → Complex) (z : Complex) : Complex :=
  ∑ a, value a * finiteLagrangeBasis position a z

end
