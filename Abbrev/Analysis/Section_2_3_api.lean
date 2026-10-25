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


namespace Chapter2

abbrev Nat.zero_mul (m : Nat) : 0 * m = 0 := @_root_.Nat.Mul0.eq.Zero m

abbrev Nat.succ_mul (n m : Nat) : (n++) * m = n * m + m := @_root_.Nat.Mul.eq.AddMul n m

abbrev Nat.one_mul' (m : Nat) : 1 * m = 0 + m := @_root_.Nat.Mul1.eq.Add0 m

abbrev Nat.one_mul (m : Nat) : 1 * m = m := @_root_.Nat.Eq1Mul m

abbrev Nat.two_mul (m : Nat) : 2 * m = 0 + m + m := @_root_.Nat.Mul2.eq.AddAdd0 m

abbrev Nat.mul_one (m : Nat) : m * 1 = m := @_root_.Nat.Eq_Mul1 m

abbrev Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := @_root_.Nat.MulAddEqAddMulS a b c

abbrev Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := @_root_.Nat.EqAddMulAddMulS a b c

abbrev Nat.mul_lt_mul_of_pos_right {a b c : Nat} (h : a < b) (hc : c.IsPos) : a * c < b * c :=
  _root_.Nat.Mul.lt.Mul.of.IsPos.Lt h hc

abbrev Nat.mul_gt_mul_of_pos_right {a b c : Nat} (h : a > b) (hc : c.IsPos) : a * c > b * c :=
  _root_.Nat.Mul.gt.Mul.of.IsPos.Gt h hc

abbrev Nat.mul_lt_mul_of_pos_left {a b c : Nat} (h : a < b) (hc : c.IsPos) : c * a < c * b :=
  _root_.Nat.LtMul.of.IsPos.Lt h hc

abbrev Nat.mul_gt_mul_of_pos_left {a b c : Nat} (h : a > b) (hc : c.IsPos) : c * a > c * b :=
  _root_.Nat.GtMul.of.IsPos.Gt h hc

abbrev Nat.mul_cancel_right {a b c : Nat} (h : a * c = b * c) (hc : c.IsPos) : a = b :=
  _root_.Nat.Eq.of.IsPos.Mul h hc

@[simp] abbrev Nat.pow_zero (m : Nat) : m ^ (0 : Nat) = 1 := @_root_.Nat.Pow_0.eq.One m

@[simp] abbrev Nat.zero_pow_zero : (0 : Nat) ^ 0 = 1 := _root_.Nat.Pow0S.eq.One

abbrev Nat.pow_succ (m n : Nat) : (m : Nat) ^ n++ = m ^ n * m := @_root_.Nat.PowNat.eq.MulPow m n

@[simp] abbrev Nat.pow_one (m : Nat) : m ^ (1 : Nat) = m := @_root_.Nat.EqPow_1 m

end Chapter2
