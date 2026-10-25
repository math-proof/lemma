/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/Taylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators


/-- A real-valued function `f` is `n`-times differentiable on the set `S` if `S` has the unique
differentiability property and, for every `m < n`, the `m`-th iterated derivative of `f` within
`S` is itself differentiable on `S`. Equivalently, the derivatives `f', f'', …, f^{(n)}` all exist
at every point of `S`. -/
def IsNTimesDiffOn (f : ℝ → ℝ) (n : ℕ) (S : Set ℝ) : Prop :=
  UniqueDiffOn ℝ S ∧ ∀ m < n, DifferentiableOn ℝ (iteratedDerivWithin m f S) S

/-- The `n`-th order Taylor polynomial of `f` centered at `x₀`, evaluated at `x`:
`P_n(x) = ∑_{k=0}^{n} f^{(k)}(x₀) / k! · (x - x₀)^k`. -/
noncomputable def taylorPolynomial (f : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k f x₀ / k.factorial) * (x - x₀) ^ k

/-- A function `f : ℝ → ℝ` has a strict local (relative) minimum at `x₀` if `f x₀ < f x` for all
`x` sufficiently close to but distinct from `x₀`. -/
def IsStrictLocalMin (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, f x₀ < f x

