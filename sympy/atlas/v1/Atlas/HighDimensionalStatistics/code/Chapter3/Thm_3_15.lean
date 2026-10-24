/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Lemma_3_13
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_11
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_13
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_11

set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory

namespace Chapter3

/-- The squared `L²` norm of a real-valued function `g` over `[0,1]`,
defined as `∫₀¹ g(x)² dx`. -/
noncomputable def L2normSq (g : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, g x ^ 2

/-- The squared empirical norm of `g` evaluated on the uniform grid `{i/n : i = 0, …, n-1}`,
defined as `(1/n) ∑ g(i/n)²`. -/
noncomputable def empiricalNormSq (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, g ((i : ℝ) / (n : ℝ)) ^ 2

/-- Sub-Gaussian noise vector: the coordinates `ε ω i` of `ε : Ω → Fin n → ℝ` are
componentwise sub-Gaussian with variance proxy `σsq`, integrable, with integrable exponentials,
and satisfying the analogous bound for arbitrary linear combinations. -/
structure IsSubGaussianNoiseVec {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop where
  bound : ∀ i : Fin n, ∀ s : ℝ,
    ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)
  integ : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => ε ω i) μ
  exp_integ : ∀ i : Fin n, ∀ s : ℝ,
    MeasureTheory.Integrable (fun ω => Real.exp (s * ε ω i)) μ
  weighted_sum_bound : ∀ (w : Fin n → ℝ), ∀ s : ℝ,
    ∫ ω, Real.exp (s * ∑ i, w i * ε ω i) ∂μ ≤
      Real.exp (σsq * (∑ i, w i ^ 2) * s ^ 2 / 2)

/-- Coerce an `IsSubGaussianNoiseVec` witness to its componentwise MGF bound. -/
instance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {ε : Ω → Fin n → ℝ} {σsq : ℝ} {μ : Measure Ω} :
    CoeFun (IsSubGaussianNoiseVec ε σsq μ)
      (fun _ => ∀ i : Fin n, ∀ s : ℝ,
        ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)) where
  coe := IsSubGaussianNoiseVec.bound

/-- The trigonometric linear combination `∑_{j=0}^{M-1} θ_j · φ_{j+1}(x)` where
`φ_k` denotes the `k`-th element of the trigonometric basis. -/
noncomputable def trigLinComb (M : ℕ) (θ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin M, θ j * trigBasis (j.val + 1) x

/-- `θhat` is a least-squares estimator for the trigonometric regression: for every
`ω` it minimizes the empirical squared error `∑ (Y_i - φ_θ(i/n))²` over all `θ`. -/
def IsLSEstimator {Ω : Type*} {n M : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin M → ℝ) : Prop :=
  ∀ ω θ,
    ∑ i : Fin n, (Y ω i - trigLinComb M (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 ≤
    ∑ i : Fin n, (Y ω i - trigLinComb M θ ((i : ℝ) / (n : ℝ))) ^ 2
