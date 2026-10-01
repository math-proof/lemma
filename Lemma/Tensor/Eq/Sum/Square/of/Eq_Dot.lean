import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℂ}
  {i j : Fin n}
-- given
  (h : x ᵥ* swapMatrix i j = y) :
-- imply
  ∑ k, x k ^ 2 = ∑ k, y k ^ 2 := by
-- proof
  have vm : ∀ (y : Fin n → ℂ) (i j : Fin n), y ᵥ* swapMatrix i j = y ∘ Equiv.swap i j := by
    intro y i j
    funext c
    simp only [Matrix.vecMul, dotProduct, swapMatrix, Matrix.of_apply, mul_ite, mul_one, mul_zero, Function.comp_apply]
    rw [Finset.sum_eq_single (Equiv.swap i j c) (fun e _ he => if_neg (fun h => he (by rw [h, Equiv.swap_apply_self])))
      (fun h => absurd (Finset.mem_univ _) h), if_pos (Equiv.swap_apply_self i j c).symm]
  rw [← h, vm]
  exact (Equiv.sum_comp (Equiv.swap i j) (fun k => x k ^ 2)).symm


@[main]
private lemma double_limits
  {n : ℕ}
  {x y : Fin n → ℂ}
  {i j : Fin n}
-- given
  (h : x ᵥ* swapMatrix i j = y) :
-- imply
  ∑ a, ∑ b ∈ Finset.univ.filter (· < a), (x a - x b) ^ 2 = ∑ a, ∑ b ∈ Finset.univ.filter (· < a), (y a - y b) ^ 2 := by
-- proof
  have vm : ∀ (y : Fin n → ℂ) (i j : Fin n), y ᵥ* swapMatrix i j = y ∘ Equiv.swap i j := by
    intro y i j
    funext c
    simp only [Matrix.vecMul, dotProduct, swapMatrix, Matrix.of_apply, mul_ite, mul_one, mul_zero, Function.comp_apply]
    rw [Finset.sum_eq_single (Equiv.swap i j c) (fun e _ he => if_neg (fun h => he (by rw [h, Equiv.swap_apply_self])))
      (fun h => absurd (Finset.mem_univ _) h), if_pos (Equiv.swap_apply_self i j c).symm]
  have key : ∀ z : Fin n → ℂ, ∑ a, ∑ b ∈ Finset.univ.filter (· < a), (z a - z b) ^ 2 = (∑ a, ∑ b, (z a - z b) ^ 2) / 2 := by
    intro z
    simp only [Finset.sum_filter]
    have e2 : ∑ a, ∑ b, (if a < b then (z a - z b) ^ 2 else 0) = ∑ a, ∑ b, (if b < a then (z a - z b) ^ 2 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    have e3 : ∑ a, ∑ b, (z a - z b) ^ 2 =
        ∑ a, ∑ b, (if b < a then (z a - z b) ^ 2 else 0) + ∑ a, ∑ b, (if a < b then (z a - z b) ^ 2 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rcases lt_trichotomy a b with hab | hab | hab
      · rw [if_neg (not_lt.mpr hab.le), if_pos hab, zero_add]
      · subst hab
        simp
      · rw [if_pos hab, if_neg (not_lt.mpr hab.le), add_zero]
    rw [e3, e2]
    ring
  rw [key x, key y, ← h, vm]
  congr 1
  symm
  apply Fintype.sum_equiv (Equiv.swap i j)
  intro a
  exact Fintype.sum_equiv (Equiv.swap i j) _ _ (fun b => rfl)


@[main]
private lemma offset
  {n : ℕ}
  {x y : Fin n → ℂ}
  {i j : Fin n}
  {a : ℂ}
-- given
  (h : x ᵥ* swapMatrix i j = y) :
-- imply
  ∑ k, (x k - a) ^ 2 = ∑ k, (y k - a) ^ 2 := by
-- proof
  have vm : ∀ (y : Fin n → ℂ) (i j : Fin n), y ᵥ* swapMatrix i j = y ∘ Equiv.swap i j := by
    intro y i j
    funext c
    simp only [Matrix.vecMul, dotProduct, swapMatrix, Matrix.of_apply, mul_ite, mul_one, mul_zero, Function.comp_apply]
    rw [Finset.sum_eq_single (Equiv.swap i j c) (fun e _ he => if_neg (fun h => he (by rw [h, Equiv.swap_apply_self])))
      (fun h => absurd (Finset.mem_univ _) h), if_pos (Equiv.swap_apply_self i j c).symm]
  rw [← h, vm]
  exact (Equiv.sum_comp (Equiv.swap i j) (fun k => (x k - a) ^ 2)).symm


-- created on 2026-09-27
