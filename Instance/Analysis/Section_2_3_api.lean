module
public import Instance.Analysis.Section_2_3.Part2
public import Theorem.Nat.Mul0.eq.Zero
public import Theorem.Nat.Mul.eq.AddMul
public import Theorem.Nat.Mul1.eq.Add0
public import Theorem.Nat.Eq1Mul
public import Theorem.Nat.Mul2.eq.AddAdd0
public import Theorem.Nat.Eq_Mul1
public import Theorem.Nat.MulAddEqAddMulS
public import Theorem.Nat.EqAddMulAddMulS
public import Theorem.Nat.Mul.lt.Mul.of.IsPos.Lt
public import Theorem.Nat.Mul.gt.Mul.of.IsPos.Gt
public import Theorem.Nat.LtMul.of.IsPos.Lt
public import Theorem.Nat.GtMul.of.IsPos.Gt
public import Theorem.Nat.Eq.of.IsPos.Mul
public import Theorem.Nat.Pow_0.eq.One
public import Theorem.Nat.Pow0S.eq.One
public import Theorem.Nat.PowNat.eq.MulPow
public import Theorem.Nat.EqPow_1
public import Abbrev.Analysis.Section_2_3_api


public section

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
