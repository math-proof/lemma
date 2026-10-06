import Mathlib
import sympy.Basic


/--
[Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd.lean)
-/
@[main]
private lemma main
  {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  {p : ℕ} [CharP R p]
  {T : Module.End R V}
  {d n : ℕ}
-- given
  (hd : T ^ d = 1)
  (hdn : p * d ∣ n) :
-- imply
  ∑ i ∈ Finset.range n, T ^ i = 0 := by
-- proof
  obtain ⟨c, rfl⟩ := hdn
  have hblock : ∀ m : ℕ, ∑ i ∈ Finset.range (d * m), T ^ i = m • ∑ i ∈ Finset.range d, T ^ i := by
    intro m
    induction m with
    | zero => rw [mul_zero, Finset.sum_range_zero, zero_smul]
    | succ m ih =>
      rw [mul_add, mul_one, Finset.sum_range_add, ih, add_smul, one_smul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, hd, one_pow, one_mul]
  rw [show p * d * c = d * (p * c) by ring, hblock, mul_smul, ← Nat.cast_smul_eq_nsmul R p,
    CharP.cast_eq_zero, zero_smul]


-- created on 2026-10-05
