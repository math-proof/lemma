import Mathlib.RingTheory.Polynomial.Vieta
import sympy.Basic
import sympy.sets.sets
open Polynomial


@[main]
private lemma main
  [CommRing α]
-- given
  (x : α)
  (t : Fin n → α) :
-- imply
  ∏ i : Fin n, (x - t i) = ∑ k ∈ range (n + 1), (-1) ^ k * (∑ s ∈ Finset.univ.powersetCard k, ∏ i ∈ s, t i) * x ^ (n - k) := by
-- proof
  have hpoly := Multiset.prod_X_sub_X_eq_sum_esymm ((Finset.univ : Finset (Fin n)).val.map t)
  have hcard : Multiset.card ((Finset.univ : Finset (Fin n)).val.map t) = n := by
    simp
  rw [hcard] at hpoly
  apply_fun (eval x) at hpoly
  refine Eq.trans ?_ (hpoly.trans ?_)
  ·
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    simp [Finset.prod_eq_multiset_prod]
  ·
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_pow, eval_X]
    rw [Finset.esymm_map_val]
    ac_rfl


-- created on 2018-11-15
-- updated on 2026-08-22
