import Mathlib
import sympy.Basic

open Polynomial Module
open scoped DirectSum

/--
[Nat_eq_of_forall_dvd_sum_divisors_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Nat_eq_of_forall_dvd_sum_divisors_eq.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {m m' : ℕ → ℕ}
-- given
  (hn : 0 < n)
  (h : ∀ e, e ∣ n → ∑ d ∈ e.divisors, m d = ∑ d ∈ e.divisors, m' d) :
-- imply
  ∀ d, d ∣ n → m d = m' d := by
-- proof
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    have key := h d hd
    rw [← Nat.insert_self_properDivisors hdpos.ne', Finset.sum_insert Nat.self_notMem_properDivisors,
      Finset.sum_insert Nat.self_notMem_properDivisors] at key
    have hproper : ∑ i ∈ d.properDivisors, m i = ∑ i ∈ d.properDivisors, m' i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Nat.mem_properDivisors] at hi
      exact ih i hi.2 (hi.1.trans hd)
    rw [hproper] at key
    exact Nat.add_right_cancel key


-- created on 2026-10-05
