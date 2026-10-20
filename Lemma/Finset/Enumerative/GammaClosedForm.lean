import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GammaClosedForm
open MetaMathlibExt


/--
[gamma_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GammaClosedForm.lean)
-/
@[path]
private lemma gamma_closed_form_eq
  :
-- imply
  ∀ (γ : ℕ → ℕ → ℝ),
    (∀ n : ℕ, γ n 0 = 1) →
    (∀ n : ℕ, 1 ≤ n → γ (2 * n - 1) n = 0) →
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k ≤ n / 2 →
    γ n k = (1 + 2 * (k : ℝ) / ((n : ℝ) + 2)) * γ (n - 1) k +
    (2 * (k : ℝ) - (n : ℝ) - 1) / ((n : ℝ) + 2) * γ (n - 1) (k - 1)) →
    ∀ n k : ℕ, k ≤ n / 2 →
    γ n k = (-1 / 4 : ℝ) ^ k * (Nat.choose n (2 * k) : ℝ) * (catalan k : ℝ) := by
-- proof
  apply MetaMathlibExt.gamma_closed_form


-- created on 2026-10-20
