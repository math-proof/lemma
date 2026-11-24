import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.limits.domain_defined


@[path]
private lemma main
  {a d n : ℤ}
  {f : ℤ → ℤ → Prop} :
-- imply
  (∀ j, a + 1 ≤ j → j < n → ∀ i, a + d ≤ i → i < j + d → f i j) ↔ ∀ i, a + d ≤ i → i < n - 1 + d → ∀ j, i - d + 1 ≤ j → j < n → f i j := by
-- proof
  constructor
  ·
    intro h i hi₀ hi₁ j hj₀ hj₁
    exact h j (by omega) hj₁ i hi₀ (by omega)
  ·
    intro h j hj₀ hj₁ i hi₀ hi₁
    exact h i hi₀ (by omega) j (by omega) hj₁


-- created on 2022-01-24
-- updated on 2026-11-24
