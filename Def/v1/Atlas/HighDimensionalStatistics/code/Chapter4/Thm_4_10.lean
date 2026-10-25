/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_8
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Thm_4_8
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Thm_4_10_Bridges
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_10_Bridges
open MeasureTheory Matrix Real Finset BigOperators


namespace Rigollet.Chapter4.Thm_4_10

noncomputable section

set_option linter.unusedVariables false

variable {d : ℕ}

/-- The operator norm of a square real matrix, defined via the associated Euclidean-space
linear map's continuous-linear-map norm. -/
def matOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- A random vector `X : Omega → Fin d → ℝ` is sub-Gaussian with parameter `sigma_sq`
under `mu` if it has zero mean and every one-dimensional projection `⟨u, X⟩` (over unit
vectors `u`) has moment generating function bounded by `exp (sigma_sq * s^2 / 2)`. -/
def IsSubGaussianVector {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (X : Omega → Fin d → ℝ) (sigma_sq : ℝ) : Prop :=
  AEMeasurable X mu ∧
  (∀ j : Fin d, ∫ omega, X omega j ∂mu = 0) ∧
  ∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      Integrable (fun omega => Real.exp (s * (∑ j : Fin d, u j * X omega j))) mu ∧
      ∫ omega, Real.exp (s * (∑ j : Fin d, u j * X omega j)) ∂mu ≤
        Real.exp (sigma_sq * s ^ 2 / 2)

/-- The empirical covariance matrix `(1/n) ∑_i X_i X_iᵀ` of `n` sample vectors. -/
def empiricalCov {n : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ) (omega : Omega) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (n : ℝ)) • ∑ i : Fin n, Matrix.of (fun (j k : Fin d) => X i omega j * X i omega k)

/-- The `ℓ₀` "norm" of a vector: the number of nonzero entries. -/
def l0norm (v : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

/-- The outer product `v v^⊤` of a vector with itself, viewed as a matrix. -/
def outerProduct (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun i j => v i * v j)

/-- `sigMat` is a spiked covariance matrix with spike strength `theta` and direction `v`
if `sigMat = θ v vᵀ + I`. -/
def IsSpikedCovariance (sigMat : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (v : Fin d → ℝ) : Prop :=
  sigMat = theta • outerProduct v + (1 : Matrix (Fin d) (Fin d) ℝ)

/-- `v` is the `k`-sparse largest eigenvector of `M`: it is a unit vector with at most
`k` nonzero entries, and its Rayleigh quotient is maximal among all `k`-sparse unit
vectors. -/
def IsKSparseLargestEigenvector (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (k : ℕ) : Prop :=
  dotProduct v v = 1 ∧ l0norm v ≤ k ∧
  ∀ u : Fin d → ℝ, dotProduct u u = 1 → l0norm u ≤ k →
    dotProduct v (M.mulVec v) ≥ dotProduct u (M.mulVec u)

/-- Wraps Thm 4.8's `IsLargestEigenvector` predicate for vectors indexed by `Fin d`,
transferring the `Fin d → ℝ` argument into Euclidean space. -/
def IsLargestEigenvectorFin (M : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) : Prop :=
  Thm48.IsLargestEigenvector M (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))

/-- The sparse PCA rate appearing in Theorem 4.10: it controls the deviation of the
empirical covariance from the population covariance and is essentially
`max(√(t/n), t/n)` for `t ≍ k log(d/k) + log(1/δ)`. -/
def sparsePCARate (d k n : ℕ) (delta : ℝ) : ℝ :=
  let t := (2 * (k : ℝ)) * Real.log 288 + (2 * (k : ℝ)) * Real.log (Real.exp 1 * (d : ℝ) / (2 * (k : ℝ))) + Real.log (1 / delta)
  max (32 * Real.sqrt (2 * t / (n : ℝ))) (64 * t / (n : ℝ))

/-- The Euclidean (`ℓ²`) norm of a vector `f : Fin d → ℝ`. -/
def euclideanNorm (f : Fin d → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin d))‖

/-- Sign-invariant distance between `vhat` and `v`: the smaller of `‖vhat - v‖` and
`‖vhat + v‖`, since eigenvectors are determined only up to sign. -/
def signInvariantDist (vhat v : Fin d → ℝ) : ℝ :=
  min (euclideanNorm (vhat - v)) (euclideanNorm (vhat + v))

/-- The absolute constant `C` appearing in the final sparse PCA bound. Here we take
`C = 3`. -/
noncomputable def sparse_pca_C : ℝ := 3

/-- The "bad event" associated to a coordinate subset `s`: the set of `omega` for which
some unit vector supported on `s` exhibits a large deviation of the empirical Rayleigh
quotient from the population value. -/
def submatrixBadEvent {n : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (s : Finset (Fin d)) (t : ℝ) : Set Omega :=
  {omega : Omega |
    ∃ (x : Fin d → ℝ), (∀ i, i ∉ s → x i = 0) ∧ dotProduct x x = 1 ∧
    |dotProduct x ((empiricalCov X omega - covMat).mulVec x)| > matOpNorm covMat * t}

/-- Restricted-coordinate concentration bound: the probability that the operator-norm
deviation `‖Σ̂_sub - Σ_sub‖` exceeds `‖Σ_sub‖ · t` is bounded by
`288^m · exp(-(n/2) · min(t²/32², t/32))`. -/
def vectorSupport (v : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => v i ≠ 0

/-- `HasSparseWitness` asserts that whenever the operator-norm deviation
`‖Σ̂ - Σ‖` exceeds `‖Σ‖ · t`, there is a `2k`-sparse unit vector `w` witnessing this
deviation via its quadratic form. -/
def HasSparseWitness {d : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (k : ℕ) (t : ℝ) : Prop :=
  ∀ (omega : Omega),
    matOpNorm (empiricalCov X omega - covMat) > matOpNorm covMat * t →
    ∃ w : Fin d → ℝ, l0norm w ≤ 2 * k ∧ dotProduct w w = 1 ∧
      |dotProduct w ((empiricalCov X omega - covMat).mulVec w)| > matOpNorm covMat * t

/-- Probabilistic large-deviation bound for sparse PCA: under the spiked-covariance
hypotheses, the probability of a large operator-norm deviation is at most `δ`. -/
def sparsePCARate_textbook (d k n : ℕ) (delta : ℝ) : ℝ :=
  let t := (k : ℝ) * Real.log (Real.exp 1 * (d : ℝ) / (k : ℝ)) + Real.log (1 / delta)
  max (Real.sqrt (t / (n : ℝ))) (t / (n : ℝ))

end
end Rigollet.Chapter4.Thm_4_10
