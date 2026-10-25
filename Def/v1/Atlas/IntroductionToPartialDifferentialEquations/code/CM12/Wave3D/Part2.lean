/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.Wave3D.Part2
set_option maxHeartbeats 3200000


noncomputable section

open Matrix Real MeasureTheory Filter intervalIntegral

namespace WaveEquation3D

/-- The **angular metric** $h(X, Y) := \sum_i m(e_{(i)}, X) m(e_{(i)}, Y)$ associated
with a null frame; it is positive-definite on the $m$-orthogonal complement of
$\mathrm{span}(L, \underline L)$ and vanishes on $\mathrm{span}(L, \underline L)$. -/
def angularMetric (n : ℕ) (nf : NullFrame n) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n - 1), minkowskiInner n (nf.e i) X * minkowskiInner n (nf.e i) Y

end WaveEquation3D
end
