import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[path]
private lemma main
  {n : ℕ}
  {A B : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h : IsUnit (A + B).det) :
-- imply
  (A + B)⁻¹ * B = 1 - (A + B)⁻¹ * A := by
-- proof
  rw [eq_sub_iff_add_eq, ← Matrix.mul_add, add_comm B A, Matrix.nonsing_inv_mul _ h]


@[path]
private lemma push
  {i j k : ℕ}
  {L H : ℕ → ℕ → ℝ} :
-- imply
  ∑ t ∈ Finset.range k, L i t * H j t = ∑ t ∈ Finset.range (k + 1), L i t * H j t - L i k * H j k := by
-- proof
  rw [Finset.sum_range_succ]
  ring


-- created on 2023-04-30
