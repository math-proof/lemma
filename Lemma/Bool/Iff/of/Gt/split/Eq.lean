import Lemma.Set.Iff.of.In_Ico.split.Eq
open Set


@[main]
private lemma main
  {x y : ℕ → α}
  {n m : ℕ}
-- given
  (h₀ : n > 0)
  (h₁ : m > n) :
-- imply
  (∀ i < m, x i = y i) ↔ (∀ i < n, x i = y i) ∧ ∀ i ∈ Set.Ico n m, x i = y i :=
-- proof
  Iff.of.In_Ico.split.Eq ⟨h₀, h₁⟩


-- created on 2026-09-27
