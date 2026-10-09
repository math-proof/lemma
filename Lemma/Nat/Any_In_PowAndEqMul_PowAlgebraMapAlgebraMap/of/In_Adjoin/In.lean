import Mathlib
import sympy.Basic


/--
[Algebra_exists_pow_mul_eq_of_mem_adjoin_div](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_pow_mul_eq_of_mem_adjoin_div.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S]
  {I : Ideal R}
  {a : R}
  {x : S}
-- given
  (ha : a ∈ I)
  (hx : x ∈ Algebra.adjoin R {x : S | ∃ i ∈ I, x * algebraMap R S a = algebraMap R S i}) :
-- imply
  ∃ (n : ℕ) (c : R), c ∈ I ^ n ∧ x * algebraMap R S a ^ n = algebraMap R S c := by
-- proof
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨1, i, by simpa using hi, by simpa using hxi⟩
  | algebraMap r => exact ⟨0, r, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, c, hc, hxc⟩ := hx
    obtain ⟨m, d, hd, hyd⟩ := hy
    refine ⟨n + m, c * a ^ m + d * a ^ n, ?_, ?_⟩
    · refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]; exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ha m)
      · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hd (Ideal.pow_mem_pow ha n)
    · rw [add_mul, map_add, map_mul, map_mul, map_pow, map_pow, ← hxc, ← hyd]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, c, hc, hxc⟩ := hx
    obtain ⟨m, d, hd, hyd⟩ := hy
    refine ⟨n + m, c * d, ?_, ?_⟩
    · rw [pow_add]; exact Ideal.mul_mem_mul hc hd
    · rw [map_mul, ← hxc, ← hyd]; ring


-- created on 2026-10-05
