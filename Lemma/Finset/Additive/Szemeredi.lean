import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Additive.Szemeredi
open scoped Finset
open MathlibExt.Combinatorics.Additive.SzemerediWanted


/--
[szemeredi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szemeredi_eq
  :
-- imply
  ∀ k : ℕ, 0 < k → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset ℕ, A ⊆ Finset.range n → δ * (n : ℝ) ≤ (A.card : ℝ) →
    ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A := by
-- proof
  apply MathlibExt.Combinatorics.Additive.SzemerediWanted.szemeredi


-- created on 2026-10-20
