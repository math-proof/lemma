/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_12
import Notation.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators


noncomputable section

set_option linter.unusedVariables false

set_option maxHeartbeats 1600000

variable {d : ℕ}

namespace Rigollet.Chapter4.Thm_4_6

/-- Operator (L²) norm of a real square matrix `A`, defined as the supremum of `‖A v‖` over
unit vectors `v` in Euclidean space. -/
def matrixOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
    ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖

/-- A `Fin d → ℝ`-valued random variable `X` is sub-Gaussian with proxy variance `σ²`
(`X ~ subG_d(σ²)`) if every projection `⟨u, X⟩` along a unit vector `u` is scalar
sub-Gaussian with proxy variance `σ²`, both in Bochner and lower-Lebesgue MGF form. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin d → ℝ) (σsq : ℝ) : Prop :=
  AEMeasurable X μ ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫ ω, Real.exp (s * (∑ j : Fin d, u j * X ω j)) ∂μ ≤
        Real.exp (σsq * s ^ 2 / 2)) ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (∑ j : Fin d, u j * X ω j))) ∂μ ≤
        ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)))

/-- Empirical (sample) covariance matrix
`Σ̂(ω) = (1/n) Σᵢ Xᵢ(ω) Xᵢ(ω)^⊤` for `Fin d → ℝ`-valued samples. -/
def empiricalCovariance {n : ℕ} {Ω : Type*}
    (X : Fin n → Ω → Fin d → ℝ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (n : ℝ)) • ∑ i : Fin n, Matrix.of (fun (j k : Fin d) => X i ω j * X i ω k)

/-- Covariance estimation rate `√((d + log(1/δ))/n) ∨ (d + log(1/δ))/n` controlling the
operator-norm deviation of the empirical covariance matrix. -/
def covRate (d n : ℕ) (δ : ℝ) : ℝ :=
  let t := (d : ℝ) + Real.log (1 / δ)
  max (Real.sqrt (t / (n : ℝ))) (t / (n : ℝ))

/-- Quadratic form `v ↦ v^⊤ Σ v` associated with the covariance matrix `Σ`. -/
def covQuadForm (covMat : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d, ∑ k : Fin d, v j * covMat j k * v k

end Rigollet.Chapter4.Thm_4_6
end
