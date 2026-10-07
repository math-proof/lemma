import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin (n + 1) → ℂ} :
-- imply
  √(∑ i, ‖x i‖ ^ 2) ^ 2 = √(∑ i, ‖x (Fin.castSucc i)‖ ^ 2) ^ 2 + ‖x (Fin.last n)‖ ^ 2 := by
-- proof
  have e : ∀ f : Fin (n + 1) → ℂ, √(∑ i, ‖f i‖ ^ 2) ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
    fun _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have e2 : ∀ f : Fin n → ℂ, √(∑ i, ‖f i‖ ^ 2) ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
    fun _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [e2, e, Fin.sum_univ_castSucc]


-- created on 2023-06-24
