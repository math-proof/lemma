import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[main]
private lemma shift
  {i j k : ℕ}
  {L H : ℕ → ℕ → ℝ}
-- given
  (h : 0 < k) :
-- imply
  ∑ t ∈ Finset.range k, L i t * H j t = ∑ t ∈ Finset.Ico 1 k, L i t * H j t + L i 0 * H j 0 := by
-- proof
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot h, add_comm]


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {n : ℕ}
  {x a b : Matrix (Fin n) (Fin n) α} :
-- imply
  x * (a + b) = x * a + x * b :=
-- proof
  Matrix.mul_add x a b


-- created on 2020-11-10
