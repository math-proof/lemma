/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
open Real Set MeasureTheory intervalIntegral


noncomputable section

namespace CM9.Wave

/-- **d'Alembert's formula** for the $1{+}1$ wave equation with initial data
$u(0, x) = f(x)$, $u_t(0, x) = g(x)$:
$$u(t, x) = \tfrac{1}{2} (f(x + t) + f(x - t)) + \tfrac{1}{2} \int_{x - t}^{x + t}
g(z) \, dz.$$ -/
def dAlembertFormula (f g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2) * (f (x + t) + f (x - t)) + (1/2) * ∫ z in (x - t)..(x + t), g z

end CM9.Wave
end
