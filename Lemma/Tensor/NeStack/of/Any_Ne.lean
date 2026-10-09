import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∃ i : Fin n, f i ≠ g i) :
-- imply
  (fun i : Fin n => f i) ≠ (fun i : Fin n => g i) := by
-- proof
  obtain ⟨i, hi⟩ := h
  intro he
  exact hi (congrFun he i)


-- created on 2022-01-01
