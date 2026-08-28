import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Complex.PowMul.eq.MulPowS.of.AddArgS.in.IocNegPiPi.Ne_0.Ne_0
import Lemma.Nat.Ge.of.Gt
open Complex Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.PowMul.eq.MulPowS.of.Gt_0 |
| comm | Complex.MulPowS.eq.PowMul.of.Gt_0 |
-/
@[main, comm]
private lemma main
  {r : ℝ}
-- given
  (h : r > 0)
  (z w : ℂ) :
-- imply
  (↑r * z) ^ w = (↑r : ℂ) ^ w * z ^ w := by
-- proof
  if hz : z = 0 then
    subst hz
    if hw : w = 0 then
      subst hw
      simp
    else
      rw [mul_zero, zero_cpow hw, mul_zero]
  else
    apply PowMul.eq.MulPowS.of.AddArgS.in.IocNegPiPi.Ne_0.Ne_0
      (ofReal_ne_zero.mpr (ne_of_gt h)) hz
    rw [arg_ofReal_of_nonneg (Ge.of.Gt h), zero_add]
    apply Arg.in.IocNegPiPi


-- created on 2026-08-28
