/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Uniformization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ProjectionTheory.code.UniformSet

open Finset Real

namespace UniformSet

/-- A real-valued set function `μ` is sub-additive if
`μ(A ∪ B) ≤ μ(A) + μ(B)` for all finite sets `A, B`. This is the
hypothesis used in the Uniformization Lemma (e.g. `μ(B) = |B|_δ`). -/
def IsSubAdditive {d : ℕ} (μ : Finset (Fin d → ℕ) → ℝ) : Prop :=
  ∀ A B : Finset (Fin d → ℕ), μ (A ∪ B) ≤ μ A + μ B

/-- A real-valued set function `μ` is monotone if `A ⊆ B` implies `μ A ≤ μ B`. -/
def IsMonotoneSetFn {d : ℕ} (μ : Finset (Fin d → ℕ) → ℝ) : Prop :=
  ∀ A B : Finset (Fin d → ℕ), A ⊆ B → μ A ≤ μ B

/-- `IsUniformFrom N m d k X` is the "partial" uniformity property used in the
inductive proof of the Uniformization Lemma: the set `X` is required to be
`(Δ, m)`-uniform only at scales `j ∈ {k, k+1, …, m-1}`. Taking `k = 0` recovers
the full `IsUniform` predicate; `k = m` is automatic. -/
def IsUniformFrom (N m d : ℕ) (k : ℕ) (X : Finset (Fin d → ℕ)) : Prop :=
  ∀ j : ℕ, k ≤ j → j < m →
    ∃ R : ℕ, ∀ Q : Fin d → ℕ,
      (X.filter (fun p => cubeOf N m j p = Q)).Nonempty →
      subcubeCovering N m j d X Q = R
