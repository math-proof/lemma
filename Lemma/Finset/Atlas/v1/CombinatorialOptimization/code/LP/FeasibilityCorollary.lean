import Mathlib
import Initialize.Tactic.Attr.Basic
open Matrix


/--
[feasibility_corollary_primal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/LP/FeasibilityCorollary.lean)
-/
@[path]
lemma feasibility_corollary_primal
  {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) ℝ}
  {b : Fin m → ℝ}
  {c : Fin n → ℝ}
  {y : Fin m → ℝ}
-- given
  (hy : ∀ j, c j ≤ (Aᵀ *ᵥ y) j) :
-- imply
  ∀ x : Fin n → ℝ, (A *ᵥ x = b) → (∀ j, 0 ≤ x j) → dotProduct c x ≤ dotProduct b y :=
-- proof
  fun x hAx hx => weak_duality_standard A b c x y hAx hx hy


-- created on 2026-10-23
