import Mathlib
import sympy.Basic


/--
[FrobeniusDensity_ncard_conj_gen_ne_zero_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean)
-/
@[main]
private lemma main
  [Group G] [Finite G]
  {σ τ : G} :
-- imply
  {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by
-- proof
  constructor
  · intro hne
    obtain ⟨g, k, hk, hgk⟩ := Set.nonempty_of_ncard_ne_zero hne
    exact ⟨k, hk, isConj_iff.mpr ⟨g, hgk⟩⟩
  · rintro ⟨k, hk, hconj⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact Set.ncard_ne_zero_of_mem (a := g) ⟨k, hk, hg⟩ (Set.toFinite _)


-- created on 2026-10-03
