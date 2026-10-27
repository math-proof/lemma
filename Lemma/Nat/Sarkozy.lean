import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Additive.Sarkozy.Part5
open scoped InnerProductSpace


/--
[Sarkozy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Sarkozy.lean)
-/
@[path]
private lemma furstenberg_sarkozy_is
-- given
  (A : Set ℕ)
  (h : ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
    δ * (N : ℝ) ≤ ((MathlibExt.Combinatorics.Additive.SarkozyWanted.initialSegmentCount A N : ℕ) : ℝ)) :
-- imply
  ∃ a b k : ℕ, a ∈ A ∧ b ∈ A ∧ 0 < k ∧ a < b ∧ b = a + k * k := by
-- proof
  apply MathlibExt.Combinatorics.Additive.SarkozyWanted.furstenberg_sarkozy A h


-- created on 2026-10-11
