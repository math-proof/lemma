import Lemma.Matrix.DetStack_Sum_In_Ico.eq.Prod_MulProdS.of.EqSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Finset.Fin
import Syntax.LinearAlgebra.Matrix.Notation
import Theorem.Function
open Matrix Finset


/--
The stacked falling-factorial matrix on pairwise distinct values has nonzero determinant.
-/
@[path]
private lemma main
  {r n : ℕ}
  {x : Fin r ⇀ ℂ}
  {d : Fin r ⇀ ℕ}
-- given
  (hdist : ∀ i j : Fin r, i ≠ j → x[i] ≠ x[j])
  (hsum : ∑ k : Fin r, d[k] = n) :
-- imply
  ([t < n, i < n]
    ∑ k : Fin r,
      if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d[j]) (∑ j ∈ Finset.Iic k, d[j]) then
        (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d[j]) *
          x[k] ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d[j]))
      else 0).det ≠ 0 := by
-- proof
  have hsum' : ∑ k : Fin r, d.toFun k = n := by
    simpa [Fun.getElem_eq] using hsum
  have hdist' : ∀ i j : Fin r, i ≠ j → x.toFun i ≠ x.toFun j := by
    intro i j hij
    simpa [Fun.getElem_eq] using hdist i j hij
  rw [DetStack_Sum_In_Ico.eq.Prod_MulProdS.of.EqSum (x := x.toFun) (d := d.toFun) hsum']
  refine prod_ne_zero_iff.mpr ?_
  intro k _
  apply mul_ne_zero
  ·
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    apply hdist' k j
    apply Ne.symm
    apply ne_of_lt
    simpa [mem_Iio] using hj
  ·
    refine prod_ne_zero_iff.mpr ?_
    intro j _
    apply Nat.cast_ne_zero.mpr
    apply Nat.factorial_ne_zero


-- created on 2026-10-27
