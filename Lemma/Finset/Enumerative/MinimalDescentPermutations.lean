import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MinimalDescentPermutations
open MetaMathlibExt


/--
[descent_minimal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalDescentPermutations.lean)
-/
@[path]
private lemma descent_minimal_iff_eq
  {n d : ℕ}
  {σ : ℕ → ℕ}
-- given
  (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) :
-- imply
  ((Finset.filter (fun i => σ (i + 1) < σ i) (Finset.Icc 1 (n - 1))).card = d ∧
    ∀ (k : ℕ) (τ : ℕ → ℕ), 0 < k → k < n → Set.BijOn τ (Set.Icc 1 k) (Set.Icc 1 k) →
    (∃ φ : ℕ → ℕ, Set.MapsTo φ (Set.Icc 1 k) (Set.Icc 1 n) ∧
    (∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k, a < b → φ a < φ b) ∧
    ∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k, (τ a < τ b ↔ σ (φ a) < σ (φ b))) →
    (Finset.filter (fun i => τ (i + 1) < τ i) (Finset.Icc 1 (k - 1))).card ≠ d) ↔
    ((Finset.filter (fun i => σ (i + 1) < σ i) (Finset.Icc 1 (n - 1))).card = d ∧
    ∀ i ∈ Finset.Icc 1 (n - 1), σ i < σ (i + 1) →
    2 ≤ i ∧ i ≤ n - 2 ∧
    (σ i < σ (i - 1) ∧ σ (i - 1) < σ (i + 2) ∧ σ (i + 2) < σ (i + 1) ∨
    σ i < σ (i + 2) ∧ σ (i + 2) < σ (i - 1) ∧ σ (i - 1) < σ (i + 1))) := by
-- proof
  apply MetaMathlibExt.descent_minimal_iff n d σ hσ


-- created on 2026-10-20
