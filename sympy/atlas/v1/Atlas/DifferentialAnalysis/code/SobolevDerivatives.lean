/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.FourierInversion
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TemperedDistributions
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.TemperedDistributions

open scoped SchwartzMap FourierTransform
open SobolevSpace TemperedDistributions TestFunctions MeasureTheory

noncomputable section

namespace SobolevSpace

variable (n : ℕ)

/-- The order `|α| = ∑ α i` of a multi-index `α : Fin n → ℕ`. -/
def multiIndexOrder (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- Iterated distributional partial derivative in the `i`-th coordinate, applied `k` times. -/
def iteratedPartialDerivDistrib (i : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => distribDerivCLM (F := ℂ) (EuclideanSpace.single i (1 : ℝ)) v)^[k] u

/-- The multi-index distributional derivative `D^α u`, applied coordinate by coordinate. -/
def iteratedDistribDeriv (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u

/-- Characterization of `H^m` (for integer `m ≥ 0`): every multi-index derivative `D^α u` with `|α| ≤ m` lies in `L²`. -/
def AllDerivMemL2 (m : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (α : Fin n → ℕ), multiIndexOrder n α ≤ m → MemHs n 0 (iteratedDistribDeriv n α u)
