import Lemma.Complex.ArgExpMulI.eq.Sub_Mul_Ceil
import Lemma.Complex.CeilSubDivArg.eq.Zero
open Complex
@[path]
private lemma main
  (z : ℂ) :
  arg (exp (I * arg z)) = arg z := by
  rw [ArgExpMulI.eq.Sub_Mul_Ceil (arg z)]
  have hceil : ⌈arg z / (2 * (1 : ℕ) * π) - 1 / 2⌉ = 0 :=
    CeilSubDivArg.eq.Zero z 1
  have hcast : (2 * (1 : ℕ) * π : ℝ) = 2 * π := by simp
  rw [hcast] at hceil
  rw [hceil]
  ring
-- created on 2019-03-01
