/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.ProjectionTheory.code.SelbergExpansion
open Matrix Finset BigOperators


noncomputable section

namespace SelbergExpansion

section GeneralGroup

variable {G : Type*} [Fintype G] [DecidableEq G] [Group G]

/-- The group convolution `(f₁ * f₂)(g) = ∑_{g₁} f₁(g₁) f₂(g₁⁻¹ g)` on a finite
group `G`. -/
def groupConv (f₁ f₂ : G → ℂ) (g : G) : ℂ :=
  ∑ g₁ : G, f₁ g₁ * f₂ (g₁⁻¹ * g)

/-- Right convolution operator `T_μ : f ↦ f * μ` on functions `G → ℂ`. -/
def convOp (μ : G → ℂ) (f : G → ℂ) : G → ℂ :=
  groupConv f μ

/-- Squared `ℓ²` norm of `f : G → ℂ`, i.e. `∑_{g ∈ G} ‖f(g)‖²`. -/
def l2NormSq (f : G → ℂ) : ℝ :=
  ∑ g : G, ‖f g‖ ^ 2

/-- A function `f : G → ℂ` is *mean zero* if `∑_{g ∈ G} f(g) = 0`. -/
def IsMeanZero (f : G → ℂ) : Prop :=
  ∑ g : G, f g = 0

/-- The "second-largest" singular value `σ₁(T_μ)` of the convolution operator
`T_μ`, defined as the supremum of `‖T_μ f‖_{ℓ²} / ‖f‖_{ℓ²}` over nonzero
mean-zero `f`. Smaller `σ₁` means better spectral gap / expansion. -/
def sigma1 (μ : G → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
    r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)}

/-- The uniform probability measure on a finite set `A ⊆ G`:
`g ↦ 1/|A|` if `g ∈ A`, else `0`. -/
def uniformMeasure (A : Finset G) (g : G) : ℂ :=
  if g ∈ A then (1 : ℂ) / (A.card : ℂ) else 0

/-- Number of edges in the Cayley graph on `G` with generators `A` going from
`S` to `T`: pairs `(s, t) ∈ S × T` with `s⁻¹ t ∈ A`. -/
def cayleyEdgeCount (A : Finset G) (S T : Finset G) : ℕ :=
  ((S ×ˢ T).filter (fun p => p.1⁻¹ * p.2 ∈ A)).card

/-- A measure `μ : G → ℂ` is *symmetric* if `μ(g) = μ(g⁻¹)` for every `g`. -/
def IsSymmetricMeasure (μ : G → ℂ) : Prop :=
  ∀ g : G, μ g = μ g⁻¹

/-- Convolution powers of `μ`: `μ^{*0}` is the delta at the identity, and
`μ^{*(n+1)} = μ^{*n} * μ`. -/
def convPow (μ : G → ℂ) : ℕ → (G → ℂ)
  | 0 => fun g => if g = 1 then 1 else 0
  | n + 1 => groupConv (convPow μ n) μ

end GeneralGroup
end SelbergExpansion
end
