/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Cor_4_9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Matrix.LDL
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_8
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Thm_4_8
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Thm_4_6
import Notation.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6
open MeasureTheory Matrix Real Finset BigOperators ProbabilityTheory
open scoped Matrix.Norms.L2Operator


noncomputable section

set_option linter.unusedVariables false

namespace Cor49

variable {d : ℕ}

/-- A `d × d` real matrix `S` is a *spiked covariance* with signal strength `θ > 0` along the
unit direction `v ∈ ℝ^d` if `S = θ · v v^⊤ + I_d`. This is the matrix appearing in the PCA
model of Corollary 4.9. -/
def IsSpikedCovariance (S : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < θ ∧ ‖v‖ = 1 ∧ S = θ • (vecMulVec v v) + (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The operator (L²) norm of a real square matrix `A`, defined via the associated continuous
linear map on Euclidean space. -/
noncomputable def matrixOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- The empirical (sample) covariance matrix
`Σ̂(ω) = (1/n) Σᵢ Xᵢ(ω) Xᵢ(ω)^⊤` of `n` Euclidean-vector-valued samples `X₁, …, Xₙ`. -/
def empiricalCovariance {n : ℕ} {Ω : Type*}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (n : ℝ)) • ∑ i : Fin n, Matrix.of (fun (j k : Fin d) => X i ω j * X i ω k)

/-- A unit vector `w` is a *largest eigenvector* of the matrix `M` if it maximises the Rayleigh
quotient `⟨u, Mu⟩` over all unit vectors `u`. -/
def IsLargestEigenvector
    (M : Matrix (Fin d) (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) : Prop :=
  ‖w‖ = 1 ∧
  ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ u)
      (M.mulVec (EuclideanSpace.equiv (Fin d) ℝ u)) ≤
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ w)
      (M.mulVec (EuclideanSpace.equiv (Fin d) ℝ w))

/-- A Euclidean-vector valued random variable `X` is sub-Gaussian with proxy variance `σ²`
(written `X ~ subG_d(σ²)`) if for every unit vector `u`, the projection `⟨u, X⟩` is a
scalar sub-Gaussian random variable with proxy variance `σ²`, both for the Bochner and the
lower-Lebesgue MGF bound. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ) : Prop :=
  AEMeasurable X μ ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫ ω, Real.exp (s * (∑ j : Fin d, u j * X ω j)) ∂μ ≤
        Real.exp (σsq * s ^ 2 / 2)) ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (∑ j : Fin d, u j * X ω j))) ∂μ ≤
        ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)))

/-- The covariance estimation rate `√((d + log(1/δ))/n) ∨ (d + log(1/δ))/n` that controls the
operator-norm error of the empirical covariance matrix. -/
def covRate (d₀ n : ℕ) (delta : ℝ) : ℝ :=
  let t := (d₀ : ℝ) + Real.log (1 / delta)
  max (Real.sqrt (t / (n : ℝ))) (t / (n : ℝ))

/-- The universal constant `C₁ = 1024` appearing in the operator-norm concentration bound
for the empirical covariance matrix. -/
noncomputable def opNorm_concentration_C₁ : ℝ := 1024

/-- Convert a family of Euclidean-space-valued random variables to "plain" `Fin d → ℝ`-valued
random variables by forgetting the `L²` structure. -/
def toPlainVec {n : ℕ} {Ω : Type*}
    (Y : Fin n → Ω → EuclideanSpace ℝ (Fin d)) : Fin n → Ω → Fin d → ℝ :=
  fun i ω j => Y i ω j

/-- Apply a matrix `M` to a Euclidean-space vector `x`, transporting through `WithLp.equiv`. -/
def applyMatrix (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (M *ᵥ (WithLp.equiv 2 (Fin d → ℝ) x))

end Cor49
end
