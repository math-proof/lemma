import Lemma.Complex.ArgExpMulI.eq.Sub_Mul_Ceil
import Lemma.Complex.CeilSubDivArg.eq.Zero
open Complex


@[main]
private lemma main
-- given
  (z : ℂ)
  (n : ℕ) :
-- imply
  arg ((I * (arg z / n)).exp) = arg z / n := by
-- proof
  have hcast : I * (arg z / n : ℂ) = I * (arg z / n : ℝ) := by
    simp [div_eq_mul_inv]
  rw [hcast, ArgExpMulI.eq.Sub_Mul_Ceil]
  have hceil : ⌈(arg z / n) / (2 * π) - 1 / 2⌉ = 0 := by
    simpa [div_div, mul_assoc, mul_left_comm, mul_comm] using
      CeilSubDivArg.eq.Zero z n
  rw [hceil]
  simp


-- created on 2018-11-06
-- updated on 2026-08-23
