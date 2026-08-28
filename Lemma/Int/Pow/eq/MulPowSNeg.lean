import Lemma.Int.MulNegS.eq.Mul
import Lemma.Nat.PowMul.eq.MulPowS
open Int Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Pow.eq.MulPowSNeg |
| comm | Int.MulPowSNeg.eq.Pow |
-/
@[main, comm]
private lemma main
  [CommRing α]
  {x : α}
  {n : ℕ} :
-- imply
  x ^ n = (-1) ^ n * (-x) ^ n := calc
-- proof
  _ = (1 * x) ^ n := by
    simp [one_mul]
  _ = ((-1) * (-x)) ^ n := by
    rw [← MulNegS.eq.Mul]
  _ = (-1) ^ n * (-x) ^ n := by
    apply PowMul.eq.MulPowS


-- created on 2018-11-14
-- updated on 2026-08-28
