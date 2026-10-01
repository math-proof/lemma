import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma pop
  {n : ℕ}
  {x : ℕ → ℂ}
-- given
  (h : 0 < n) :
-- imply
  √(∑ i ∈ Finset.range n, ‖x i‖ ^ 2) ^ 2 = √(∑ i ∈ Finset.range (n - 1), ‖x i‖ ^ 2) ^ 2 + ‖x (n - 1)‖ ^ 2 := by
-- proof
  have e : ∀ (s : Finset ℕ) (f : ℕ → ℂ), √(∑ i ∈ s, ‖f i‖ ^ 2) ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 :=
    fun _ _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [e, e]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
  simp [Finset.sum_range_succ]


-- created on 2023-06-24
