/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexSatisfiesMultiplicativeBetheEquations
    (c : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Prop :=
  ∀ j, Complex.exp (Complex.I * ((N : ℝ) * p j)) =
    (-1 : ℂ) ^ (n - 1) *
      Complex.exp (-Complex.I * ∑ k, sixVertexTheta c (p j) (p k))

end
end StatMech.FrontierD
