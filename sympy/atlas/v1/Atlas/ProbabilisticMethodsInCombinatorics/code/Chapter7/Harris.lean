/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter7/Harris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.UpperLower.Basic

open Finset Fintype MeasureTheory Set

noncomputable section

namespace Harris

/-- Product weight for the Bernoulli product measure on $\{0,1\}^n$: assigns to a
configuration $\omega : \text{Fin } n \to \text{Bool}$ the weight
$\prod_i p_i^{\omega_i} (1 - p_i)^{1 - \omega_i}$. -/
def prodWeight (n : ℕ) (p : Fin n → ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, bif ω i then p i else 1 - p i

/-- Probability of an event $S \subseteq \{0,1\}^n$ under the Bernoulli product
measure with parameters $p$, defined as $\sum_\omega \text{prodWeight}(\omega) \cdot \mathbf{1}_S(\omega)$. -/
def P (n : ℕ) (p : Fin n → ℝ) (S : Set (Fin n → Bool)) : ℝ :=
  ∑ ω : Fin n → Bool, prodWeight n p ω * S.indicator (fun _ => (1 : ℝ)) ω

/-- General product weight on $\alpha^n$ for a linearly ordered finite type $\alpha$:
$\mu(\omega) = \prod_i p_i(\omega_i)$. -/
def generalProdWeight (n : ℕ) (α : Type*) [LinearOrder α] [Fintype α]
    (p : Fin n → α → ℝ) (ω : Fin n → α) : ℝ :=
  ∏ i : Fin n, p i (ω i)

/-- General expectation operator: $\mathbb{E}[f] = \sum_\omega \mu(\omega) f(\omega)$
under the product weight on $\alpha^n$. -/
def generalE (n : ℕ) (α : Type*) [LinearOrder α] [Fintype α]
    (p : Fin n → α → ℝ) (f : (Fin n → α) → ℝ) : ℝ :=
  ∑ ω : Fin n → α, generalProdWeight n α p ω * f ω
