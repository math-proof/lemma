/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Problem_4_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Matrix Finset

namespace Chapter4.Problem41

noncomputable section

/-- Squared Frobenius norm of a real matrix, $\sum_{i,j} A_{ij}^2$. -/
def frobeniusNormSq {m p : Type*} [Fintype m] [Fintype p]
    (A : Matrix m p ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The entrywise $\ell_0$ "norm" of a matrix: the number of nonzero entries. -/
def matrixL0Norm {m p : Type*} [Fintype m] [Fintype p] [DecidableEq ℝ]
    (M : Matrix m p ℝ) : ℕ :=
  (univ ×ˢ univ).filter (fun ij => M ij.1 ij.2 ≠ 0) |>.card

/-- A real-valued random variable `X` is sub-Gaussian with proxy variance `σsq` if its
moment generating function satisfies $\mathbb{E}[e^{tX}] \le e^{t^2 \sigma^2 / 2}$ for every `t`. -/
def IsSubGaussian {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * σsq / 2)

/-- A random matrix `E` is sub-Gaussian with proxy variance `σsq` if for every pair of unit
vectors `u, v` the scalar $u^\top E v$ is sub-Gaussian with proxy `σsq`. -/
def IsSubGaussianMatrix {Ω : Type*} [MeasurableSpace Ω] {n T : ℕ}
    (E : Ω → Matrix (Fin n) (Fin T) ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop :=
  ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin T)),
    ‖u‖ = 1 → ‖v‖ = 1 →
    IsSubGaussian (fun ω => dotProduct (EuclideanSpace.equiv (Fin n) ℝ u)
      ((E ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ v))) σsq μ
