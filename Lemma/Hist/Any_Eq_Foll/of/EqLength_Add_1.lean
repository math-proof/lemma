import sympy.stats.mdp_history
import sympy.Basic


@[main]
private lemma main
  {S : Type*} {A : Type*}
  {h : Hist S A}
  {t : ℕ}
-- given
  (h₀ : h.length = t + 1) :
-- imply
  ∃ h' a s, h = Hist.foll h' a s := by
-- proof
  cases h with
  | init s =>
    simp [Hist.length] at h₀
  | foll h' a s =>
    exact ⟨h', a, s, rfl⟩


-- created on 2026-09-26
