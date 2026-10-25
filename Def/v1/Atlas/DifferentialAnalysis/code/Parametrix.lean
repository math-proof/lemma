/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.CauchyKernelIntegrability
import Def.v1.Atlas.DifferentialAnalysis.code.CauchyKernelIntegrability
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
open scoped SchwartzMap
open MvPolynomial MeasureTheory ContinuousLinearMap Filter Asymptotics


noncomputable section

namespace DifferentialOperators

/-- The Cauchy-Riemann polynomial `X₀ + i·X₁`, whose associated constant-coefficient differential
operator is the Cauchy-Riemann (`∂̄`) operator on `ℝ² ≅ ℂ`. -/
def dbarPoly : MvPolynomial (Fin 2) ℂ :=
  X 0 + C Complex.I * X 1

/-- The Cauchy-Riemann (`∂̄`) operator on tempered distributions on `ℝ²`, defined as the
constant-coefficient differential operator with symbol `dbarPoly`. -/
def dbarOp : 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  constCoeffDiffOp 2 dbarPoly

/-- The Cauchy-Riemann kernel `(2π)⁻¹·(x + iy)⁻¹` on `ℝ²`: this is the (distributional) fundamental
solution of the Cauchy-Riemann operator `∂̄`. -/
def cauchyRiemannKernel : EuclideanSpace ℝ (Fin 2) → ℂ :=
  fun v => ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((v 0 : ℂ) + Complex.I * (v 1 : ℂ))⁻¹


/-- The measurable equivalence between `EuclideanSpace ℝ (Fin 2)` (with the L² product
structure) and `ℝ × ℝ`. -/
noncomputable def euclidProdMeasurableEquiv : EuclideanSpace ℝ (Fin 2) ≃ᵐ (ℝ × ℝ) where
  toEquiv := (WithLp.equiv 2 (Fin 2 → ℝ)).trans (piFinTwoEquiv fun _ => ℝ)
  measurable_toFun := by
    show Measurable (fun v : EuclideanSpace ℝ (Fin 2) => (v 0, v 1)); fun_prop
  measurable_invFun := Continuous.measurable
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      (continuous_pi (fun i => by fin_cases i <;> continuity)))

end DifferentialOperators
end
