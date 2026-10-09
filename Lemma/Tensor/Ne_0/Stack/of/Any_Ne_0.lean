import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h : ∃ i : Fin n, f i ≠ 0) :
-- imply
  (fun i : Fin n => f i) ≠ 0 := by
-- proof
  obtain ⟨i, hi⟩ := h
  intro he
  exact hi (congrFun he i)


-- created on 2022-01-01
