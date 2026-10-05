import Mathlib
import sympy.Basic


/--
[Subring_mem_centralizer_of_mul_eq_of_mul_eq_of_forall_mul_eq_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subring_mem_centralizer_of_mul_eq_of_mul_eq_of_forall_mul_eq_mul.lean)
-/
@[main]
private lemma main
  [Ring R]
  {S : Set R}
  {ε ε' δ : R}
-- given
  (hε : ε ∈ Subring.centralizer S)
  (h₁ : ε * ε' = δ)
  (h₂ : ε' * ε = δ)
  (hδ : ∀ x : R, δ * x = x * δ)
  (hcanc : ∀ x y : R, δ * x = δ * y → x = y) :
-- imply
  ε' ∈ Subring.centralizer S := by
-- proof
  rw [Subring.mem_centralizer_iff] at hε ⊢
  intro g hg
  apply hcanc
  calc δ * (g * ε') = ε' * ε * g * ε' := by rw [← h₂]; simp only [mul_assoc]
    _ = ε' * (g * ε) * ε' := by rw [hε g hg]; simp only [mul_assoc]
    _ = ε' * g * (ε * ε') := by simp only [mul_assoc]
    _ = ε' * g * δ := by rw [h₁]
    _ = δ * (ε' * g) := by rw [hδ]


-- created on 2026-10-05
