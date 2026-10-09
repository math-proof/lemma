import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal.lean)
-/

private lemma  geomSum_sub_natCast_mem_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A] {u : A}
    (hu : u - 1 ∈ maximalIdeal A) (n : ℕ) :
    (∑ i ∈ Finset.range n, u ^ i) - (n : A) ∈ maximalIdeal A := by
  have hpow : ∀ i, u ^ i - 1 ∈ maximalIdeal A := fun i => by
    have h : u ^ i - 1 = (u - 1) * ∑ j ∈ Finset.range i, u ^ j := by
      rw [mul_comm, geom_sum_mul]
    exact h ▸ Ideal.mul_mem_right _ _ hu
  have heq : (∑ i ∈ Finset.range n, u ^ i) - (n : A) =
      ∑ i ∈ Finset.range n, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [heq]
  exact Ideal.sum_mem _ fun i _ => hpow i
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsLocalRing A]
  {u : A}
  {n : ℕ}
-- given
  (hu : u - 1 ∈ IsLocalRing.maximalIdeal A)
  (hn : IsUnit (n : A))
  (hun : u ^ n = 1) :
-- imply
  u = 1 := by
-- proof
  have hfact : (u - 1) * (∑ i ∈ Finset.range n, u ^ i) = 0 := by
    rw [mul_comm, geom_sum_mul, hun, sub_self]
  have hcof : IsUnit (∑ i ∈ Finset.range n, u ^ i) := by
    rw [← notMem_maximalIdeal]
    intro hmem
    have h := Ideal.sub_mem _ hmem (geomSum_sub_natCast_mem_maximalIdeal hu n)
    simp only [sub_sub_cancel] at h
    exact (notMem_maximalIdeal.mpr hn) h
  obtain ⟨v, hv⟩ := hcof
  have h0 : u - 1 = 0 := by
    have h := congrArg (· * (↑v⁻¹ : A)) hfact
    simp only [mul_assoc, ← hv, v.mul_inv, mul_one, zero_mul] at h
    exact h
  exact sub_eq_zero.mp h0


-- created on 2026-10-05
