import sympy.sets.sets
import sympy.Basic
open Set


@[main]
private lemma main
  {d : ℝ}
  {P : ℝ → Prop}
-- given
  (hd : 0 < d)
  (h : ∀ x ∈ Ioo (-d) d, P x) :
-- imply
  (∀ x ∈ Ioo (-d) 0, P x) ∧ (∀ x ∈ Ico 0 d, P x) := by
-- proof
  constructor
  · intro x hx
    apply h
    exact ⟨hx.1, by linarith [hx.2]⟩
  · intro x hx
    apply h
    exact ⟨by linarith [hx.1], hx.2⟩


-- created on 2026-10-03
