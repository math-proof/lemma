/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Shearer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
open Finset Real BigOperators

set_option maxHeartbeats 800000


noncomputable section

namespace Shearer

/-- Shannon entropy of a probability mass function $p : \alpha \to \mathbb{R}$:
$H(p) = \sum_x -p(x) \log p(x)$. -/
def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ x : α, negMulLog (p x)

/-- The marginal of $p$ on the first two coordinates, obtained by summing out the third. -/
def marginal12 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : α × β → ℝ :=
  fun ab => ∑ c : γ, p (ab.1, ab.2, c)

/-- The marginal of $p$ on the first and third coordinates, obtained by summing out the second. -/
def marginal13 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : α × γ → ℝ :=
  fun ac => ∑ b : β, p (ac.1, b, ac.2)

/-- The marginal of $p$ on the second and third coordinates, obtained by summing out the first. -/
def marginal23 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : β × γ → ℝ :=
  fun bc => ∑ a : α, p (a, bc.1, bc.2)

/-- The marginal of $p$ on the first coordinate, summing out both the second and third. -/
def marginal1 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : α → ℝ :=
  fun a => ∑ b : β, ∑ c : γ, p (a, b, c)

/-- The marginal of $p$ on the second coordinate, summing out both the first and third. -/
def marginal2 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : β → ℝ :=
  fun b => ∑ a : α, ∑ c : γ, p (a, b, c)

/-- The marginal of $p$ on the third coordinate, summing out both the first and second. -/
def marginal3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) : γ → ℝ :=
  fun c => ∑ a : α, ∑ b : β, p (a, b, c)

end Shearer
end
