import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Mul
import sympy.Basic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
-- given
  (P : Matrix S S ℝ)
  (x : S → ℝ) :
-- imply
  ∑ i, |(x ᵥ* P) i| ≤ (∑ j, ∑ i, |P j i|) * ∑ j, |x j| := by
-- proof
  calc
    _ ≤ ∑ i, ∑ j, |x j| * |P j i| := Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun j _ => abs_mul _ _)
    _ = ∑ j, |x j| * ∑ i, |P j i| := by
      rw [Finset.sum_comm]
      simp [Finset.mul_sum]
    _ ≤ ∑ j, |x j| * ∑ j, ∑ i, |P j i| :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun j => ∑ i, |P j i|) (fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ j)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]


-- created on 2026-09-26
