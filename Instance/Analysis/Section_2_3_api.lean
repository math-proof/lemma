import Instance.Analysis.Section_2_3.Part2
import Lemma.Nat.Mul0.eq.Zero
import Lemma.Nat.Mul.eq.AddMul
import Lemma.Nat.Mul1.eq.Add0
import Lemma.Nat.Eq1Mul
import Lemma.Nat.Mul2.eq.AddAdd0
import Lemma.Nat.Eq_Mul1
import Lemma.Nat.MulAddEqAddMulS
import Lemma.Nat.EqAddMulAddMulS
import Lemma.Nat.Mul.lt.Mul.of.IsPos.Lt
import Lemma.Nat.Mul.gt.Mul.of.IsPos.Gt
import Lemma.Nat.LtMul.of.IsPos.Lt
import Lemma.Nat.GtMul.of.IsPos.Gt
import Lemma.Nat.Eq.of.IsPos.Mul
import Lemma.Nat.Pow_0.eq.One
import Lemma.Nat.Pow0S.eq.One
import Lemma.Nat.PowNat.eq.MulPow
import Lemma.Nat.EqPow_1
import Abbrev.Analysis.Section_2_3_api


namespace Chapter2

instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

end Chapter2
