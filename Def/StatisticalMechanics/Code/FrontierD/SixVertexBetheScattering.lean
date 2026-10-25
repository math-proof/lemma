/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexScatteringDenominator (c x y : ℝ) : ℂ :=
  Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * y) -
    2 * sixVertexDelta c

end
end StatMech.FrontierD
