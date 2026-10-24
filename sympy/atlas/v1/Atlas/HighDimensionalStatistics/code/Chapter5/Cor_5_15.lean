/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_1_5_2

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_11
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Thm_5_11
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Thm_5_9
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_9

open Real MeasureTheory

noncomputable section

namespace Cor_5_15

/-- `ℓ⁰`-pseudonorm: number of nonzero coordinates of `θ`. -/
def l0norm {d : ℕ} (θ : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- The `k`-sparse `ℓ⁰`-ball `B₀(k) = {θ ∈ ℝ^d : |θ|_0 ≤ k}`. -/
def B₀ (d : ℕ) (k : ℕ) : Set (Fin d → ℝ) :=
  {θ | l0norm θ ≤ k}

/-- The conjectured minimax rate for `k`-sparse estimation in the Gaussian sequence model:
`σ² k log(e d / k) / n`. -/
def sparseRate (d k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  σ ^ 2 * k * Real.log (Real.exp 1 * d / k) / n

open Classical in
/-- Constrained least-squares estimator restricted to the `k`-sparse ball `B₀(k)`; returns `0`
if no minimizer exists. -/
def constrainedLSSparse (d k : ℕ) : Minimax.Estimator d :=
  fun Y => if h : ∃ θ ∈ B₀ d k, ∀ θ' ∈ B₀ d k, Minimax.sqDist Y θ ≤ Minimax.sqDist Y θ'
            then h.choose else fun _ => 0
