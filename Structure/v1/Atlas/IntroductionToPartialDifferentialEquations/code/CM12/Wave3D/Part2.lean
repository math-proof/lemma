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
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.Wave3D
set_option maxHeartbeats 3200000


noncomputable section

open Matrix Real MeasureTheory Filter intervalIntegral

namespace WaveEquation3D

/-- A **null frame** on $\mathbb{R}^{1+n}$ (Definition 2.2.1):
a basis $\{L, \underline L, e_{(1)}, \dots, e_{(n-1)}\}$ where $L, \underline L$ are null
with $m(L, \underline L) = -2$, and the $e_{(i)}$ are $m$-orthonormal vectors $m$-orthogonal
to both $L$ and $\underline L$. The `completeness` field records the resulting expansion
$X = -\tfrac12 m(\underline L, X) L - \tfrac12 m(L, X)\underline L + \sum_i m(e_{(i)}, X) e_{(i)}$. -/
structure NullFrame (n : ℕ) where
  L : Fin (n + 1) → ℝ
  Lb : Fin (n + 1) → ℝ
  e : Fin (n - 1) → (Fin (n + 1) → ℝ)
  L_null : minkowskiInner n L L = 0
  Lb_null : minkowskiInner n Lb Lb = 0
  L_Lb_inner : minkowskiInner n L Lb = -2
  e_orthonormal : ∀ i j : Fin (n - 1),
    minkowskiInner n (e i) (e j) = if i = j then 1 else 0
  L_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n L (e i) = 0
  Lb_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n Lb (e i) = 0
  completeness : ∀ X : Fin (n + 1) → ℝ,
    X = (-(1/2) * minkowskiInner n Lb X) • L
      + (-(1/2) * minkowskiInner n L X) • Lb
      + ∑ i, (minkowskiInner n (e i) X) • (e i)

end WaveEquation3D
end
