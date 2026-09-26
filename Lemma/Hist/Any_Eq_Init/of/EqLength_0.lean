import sympy.stats.mdp_history
import sympy.Basic


@[main]
private lemma main
  {S : Type*} {A : Type*}
  {h : Hist S A}
-- given
  (h₀ : h.length = 0) :
-- imply
  ∃ s, h = Hist.init s := by
-- proof
  cases h with
  | init s =>
    exact ⟨s, rfl⟩
  | foll _ _ _ =>
    simp [Hist.length] at h₀


-- created on 2026-09-26
