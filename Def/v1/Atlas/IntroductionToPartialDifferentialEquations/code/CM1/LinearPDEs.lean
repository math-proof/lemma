/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs


/-- The order of a multi-index $\alpha = (\alpha_1, \ldots, \alpha_n)$ is
$|\alpha| = \sum_i \alpha_i$, i.e. the total number of derivatives it represents. -/
def multiIndexOrder {n : ℕ} (α : MultiIndex' n) : ℕ := ∑ i, α i

/-- The $i$-th partial derivative $\partial_{x^i} f$ of $f : \mathbb{R}^n \to \mathbb{R}$,
defined via the Fréchet derivative applied to the $i$-th standard basis vector. -/
noncomputable def partialDerivFin {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => fderiv ℝ f x (Pi.single i 1)

/-- Iterated partial derivative along a list of coordinate indices: applies the partial
derivatives $\partial_{x^{i_1}} \partial_{x^{i_2}} \cdots$ from outermost to innermost. -/
noncomputable def iteratedPartialDeriv {n : ℕ} :
    List (Fin n) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)
  | [], f => f
  | i :: is, f => partialDerivFin i (iteratedPartialDeriv is f)

/-- Convert a multi-index $\alpha$ to a list of coordinate indices in which each $i$ is
repeated $\alpha_i$ times — the sequence of partial derivatives encoded by $\alpha$. -/
noncomputable def multiIndexToList {n : ℕ} (α : Fin n → ℕ) : List (Fin n) :=
  (Finset.univ.val.toList).flatMap (fun i => List.replicate (α i) i)

/-- The multi-index derivative $\partial^{\alpha} f = \partial_{x^1}^{\alpha_1} \cdots
\partial_{x^n}^{\alpha_n} f$, obtained by iterating partial derivatives according to the
list encoding of the multi-index $\alpha$. -/
noncomputable def multiIndexDeriv {n : ℕ} (α : Fin n → ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  iteratedPartialDeriv (multiIndexToList α) f

